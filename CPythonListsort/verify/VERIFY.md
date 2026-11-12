# Verification — development source `7a5f47d`

Run all commands below from `CPythonListsort` in the ATLAS repository.
The exported development snapshot is
`7a5f47de2501d41980fafa0a363c61c2a2fa688c`, as recorded in
[`sources/upstream-pins.md`](../sources/upstream-pins.md). This is the source
commit for the export, not the ATLAS repository's own commit ID.

## Source identity

These commands were run in the development repository immediately before the
export:

```console
$ git rev-parse main
7a5f47de2501d41980fafa0a363c61c2a2fa688c

$ git rev-parse origin/main
7a5f47de2501d41980fafa0a363c61c2a2fa688c

$ git status --porcelain
# no output
```

## Build

```console
$ lake build
Build completed successfully (8824 jobs).
```

The build emitted existing style and allowlisted `native_decide` warnings, but
no errors. It compiles the `Code` library and every one of its five layers.

## Changed and new minrun declarations: axiom audit

Create a temporary audit file and ask Lean for each declaration's transitive
axioms:

```sh
check_dir="$(mktemp -d /tmp/cpython-listsort-axioms.XXXXXX)"
check_file="$check_dir/CheckAxioms.lean"
trap 'rm -rf "$check_dir"' EXIT
cat >"$check_file" <<'EOF'
import Code

#print axioms CPythonListsort.minrunInit_exponent_eq_spec
#print axioms CPythonListsort.minrunInit_eq_spec
#print axioms CPythonListsort.cIntMinrunMask_toNat_lt_pow
#print axioms CPythonListsort.minrunNext_eq_spec
#print axioms CPythonListsort.minrunInit_stops_and_exponent_lt_64
#print axioms CPythonListsort.minrunInit_modulus_le_listSize
#print axioms CPythonListsort.minrunInit_mask_lt_modulus
#print axioms CPythonListsort.minrunNextN_output_bounds
#print axioms CPythonListsort.minrunNext_after_init_bounds
#print axioms CPythonListsort.minrun_cIntMask_truncation_regression
#print axioms CPythonListsort.minrunNextN_eq_spec
#print axioms CPythonListsort.minrunPrefixSum
#print axioms CPythonListsort.minrunSequence

#print axioms CPythonListsort.adaptiveMinrunScanInvariant_initial
#print axioms CPythonListsort.initialMergeState_package
#print axioms CPythonListsort.adaptiveMinrun_step_facts
#print axioms CPythonListsort.AdaptiveMinrunScanInvariant.advance
#print axioms CPythonListsort.listSortScanTraced_safe
#print axioms CPythonListsort.listSortImplTraced_safe
#print axioms CPythonListsort.listSortTraced_safe
#print axioms CPythonListsort.listsort_safe
#print axioms CPythonListsort.listsort_safe_keyed
#print axioms CPythonListsort.listsort_safe_unkeyed
#print axioms CPythonListsort.listSortScan_step_correct
#print axioms CPythonListsort.listSort_correct
#print axioms CPythonListsort.listsort_correct_keyed
#print axioms CPythonListsort.listsort_correct
#print axioms CPythonListsort.listSort_mergeMemory_safe
#print axioms CPythonListsort.listsort_mergeCost_bound
#print axioms CPythonListsort.listsort_mergeTree_cost_le_powerSort
EOF
lake env lean "$check_file"
rm -rf "$check_dir"
trap - EXIT
```

The following declarations all report exactly
`[propext, Classical.choice, Quot.sound]`:

- `CPythonListsort.minrunInit_exponent_eq_spec` —
  `Code/Equivalence/Minrun.lean:105`
- `CPythonListsort.minrunInit_eq_spec` —
  `Code/Equivalence/Minrun.lean:123`
- `CPythonListsort.cIntMinrunMask_toNat_lt_pow` —
  `Code/Equivalence/Minrun.lean:166`
- `CPythonListsort.minrunNext_eq_spec` —
  `Code/Equivalence/Minrun.lean:183`
- `CPythonListsort.minrunInit_stops_and_exponent_lt_64` —
  `Code/Equivalence/MinrunResults.lean:94`
- `CPythonListsort.minrunInit_modulus_le_listSize` —
  `Code/Equivalence/MinrunResults.lean:124`
- `CPythonListsort.minrunInit_mask_lt_modulus` —
  `Code/Equivalence/MinrunResults.lean:152`
- `CPythonListsort.minrunNextN_output_bounds` —
  `Code/Equivalence/MinrunResults.lean:295`
- `CPythonListsort.minrunNext_after_init_bounds` —
  `Code/Equivalence/MinrunResults.lean:309`
- `CPythonListsort.minrunNextN_eq_spec` —
  `Code/Equivalence/MinrunResults.lean:405`
- `CPythonListsort.minrunPrefixSum` —
  `Code/Equivalence/MinrunResults.lean:470`
- `CPythonListsort.minrunSequence` —
  `Code/Equivalence/MinrunResults.lean:643`

The truncation regression is separately kernel-checked with ordinary
`decide`:

```text
'CPythonListsort.minrun_cIntMask_truncation_regression'
depends on axioms: [propext, Quot.sound]
```

Its declaration is at `Code/Equivalence/MinrunResults.lean:342`. It proves
that the `e = 33` witness has actual outputs `[63, 63]`, while the ideal
full-width trace has `[63, 64]`.

## Downstream and release declarations: axiom audit

`CPythonListsort.adaptiveMinrunScanInvariant_initial` reports exactly
`[propext, Quot.sound]`.

Every other declaration below reports exactly
`[propext, Classical.choice, Quot.sound]`:

- `CPythonListsort.initialMergeState_package`
- `CPythonListsort.adaptiveMinrun_step_facts`
- `CPythonListsort.AdaptiveMinrunScanInvariant.advance`
- `CPythonListsort.listSortScanTraced_safe`
- `CPythonListsort.listSortImplTraced_safe`
- `CPythonListsort.listSortTraced_safe`
- `CPythonListsort.listsort_safe`
- `CPythonListsort.listsort_safe_keyed`
- `CPythonListsort.listsort_safe_unkeyed`
- `CPythonListsort.listSortScan_step_correct`
- `CPythonListsort.listSort_correct`
- `CPythonListsort.listsort_correct_keyed`
- `CPythonListsort.listsort_correct`
- `CPythonListsort.listSort_mergeMemory_safe`
- `CPythonListsort.listsort_mergeCost_bound`
- `CPythonListsort.listsort_mergeTree_cost_le_powerSort`

Thus the safety, correctness, stack-depth, and merge-cost release chains gain
no nonstandard axiom from the minrun revision. In particular, none depends on
a compiler-generated `native_decide` axiom.

## Gap and stale-consumer scans

```console
$ rg -n --glob '*.lean' '\b(sorry|admit)\b|^\s*axiom\b' Code Code.lean
# no matches; rg exit 1

$ rg -n --glob '*.lean' \
    'minrunInit_stops_and_shift_valid|calls_lt_of_active' Code Code.lean
# no matches; rg exit 1
```

## Native trust ledger

```console
$ python3 verify/verify_trust_boundary.py
verified native_decide trust boundary: 12 named compiler-checked regressions, no Lean consumers
```

The exact allowlisted proof leaves are:

1. `mergeAt_slide_regression`
2. `mergeAt_thirdLast_slide_regression`
3. `foundNewRunLoop_taken_merge_regression`
4. `mergeForceCollapse_threeRun_equalKey_payload_regression`
5. `listSortScan_long_run_no_extension_regression`
6. `listSortScan_policy_merge_then_push_regression`
7. `listSort_forward_keyed_duplicate_exact_regression`
8. `listSort_reverse_keyed_duplicate_exact_regression`
9. `listSort_mergeMemory_lo_event_regression`
10. `listSort_mergeMemory_hi_event_regression`
11. `listSort_mergeMemory_released_growth_regression`
12. `listSort_powerSort_cost_rotation_regression`

The new `minrun_cIntMask_truncation_regression` is absent from this list
because it uses kernel `decide`, not `native_decide`.

## Pinned-source verification

This check requires network access to the pinned CPython commit:

```console
$ python3 verify/verify_excerpts.py
verified sources/listobject-excerpts.md
verified sources/listsort.md
```

The reviewed transcription uses the 32-bit mask operation at
`Code/Transcription/Minrun.lean:47-49`. Exact quotient/remainder results carry
the explicit `mr_e < 32` premise, while the top-level scan consumes the
unconditional arbitrary-call band through
`Code/Assembly/ListSortSupport.lean:250`.

## Verdict

**PASS.** The export of development commit `7a5f47d` builds completely, has no
proof gaps, preserves the two-tier trust boundary, restricts exact minrun
equivalence honestly, and includes a kernel-checked proof of
`1 ≤ minrun ≤ 64` for every reachable call count.
