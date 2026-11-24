# Verification and historical export record

## Root integration checks

Use the root `lean-toolchain` (`leanprover/lean4:v4.36.0`) and Lake
environment. From the repository root:

```sh
lake build CSLibExt.Algorithms.Sorting.CPythonListsort
lake build CSLibExtTest.Algorithms.Sorting.CPythonListsort
python3 CSLibExt/Algorithms/Sorting/CPythonListsort/verify/verify_trust_boundary.py
python3 CSLibExt/Algorithms/Sorting/CPythonListsort/verify/test_verify_trust_boundary.py
python3 CSLibExt/Algorithms/Sorting/CPythonListsort/verify/verify_citations.py
python3 CSLibExt/Algorithms/Sorting/CPythonListsort/verify/verify_excerpts.py
scripts/check.sh
```

Building `CSLibExtTest.Algorithms.Sorting.CPythonListsort` compiles the
fixed-input checks in the mirrored test modules, including the gallop examples.
It also executes the twelve asserting `IO Unit` witnesses through their `#eval`
calls; a false assertion raises an `IO` error and fails that build. The IO
witnesses are not theorem axioms, and no production declaration depends on them.
The last command is the repository's
own gate: `scripts/check_axioms.sh` reruns `scripts/check_axioms.lean` over
every compiled module of every root library, and `scripts/check_diagnostics.sh`
rejects `sorry` and `native_decide` diagnostics.

The production API keeps namespace `CPythonListsort`; the module prefix is
`CSLibExt.Algorithms.Sorting.CPythonListsort`. The per-file disposition table
and the twelve original propositions are in
[`migration-map.json`](migration-map.json).

### What the integration was checked against

- The root aggregates cover 116 production modules and 44 test modules on Lean 4.36.0 with the
  root Mathlib pin. Fixed-input regression fixtures are in the test aggregate.
- The root policy audit checks compiled modules for forbidden axioms, unsafe declarations and
  `implemented_by` attributes outside compiler-generated exceptions, wanted declarations outside
  `WantedExt`, and forbidden cross-library imports. The local Python verifier has ten regression
  tests.
- The five principal theorems remain polymorphic in two independent universe
  parameters; the key and payload universes were not collapsed.
- Reproduction fetched the two public source files at the immutable CPython pin,
  checked their SHA-256 hashes, and ran `verify_excerpts.py` offline using those
  bytes. Both generated Markdown files matched byte for byte.
- `verify_citations.py` confirms that every `path:line` citation in this
  development's Markdown resolves to an existing, non-blank line, and that
  the roadmap trust ledger cites each of the twelve regressions at its
  `def … : IO Unit :=` line. The roadmap's pins were short by eight lines
  because the development repository it was exported from carries no license
  header; they were recomputed against this tree.

### Compatibility notes for reviewers

- 46 production modules carry a local `set_option autoImplicit true`. The
  standalone package left `autoImplicit` at Lean's default, so the imported
  statements bind their type variables implicitly; the root package sets
  `autoImplicit := false`. Each of the 46 was checked to fail without the
  option and the other 79 modules that had it were checked to compile with it
  removed, so the option now appears only where a statement needs it. It is a
  binder-elaboration setting, not a proof or trust escape.
- The CPython modules are the only part of `CSLibExt` that has not been
  converted to the Lean module system (`module` / `public import`), which is
  why they emit non-module import warnings. Converting them changes what each
  module exports and needs its own validation pass.

### What these checks do not establish

They do not establish that the Lean model refines the pinned C. The claim
boundary in [`../README.md`](../README.md) stands unchanged: the comparator
model, the excluded exception/allocator/reentrancy paths, the huge-list shift
convention, and the inline key-storage limitation are all still outside what
is proved.

## Historical standalone record

Everything below is the original standalone Lean/Mathlib 4.33.1 verification
record, kept as provenance. Its module paths (`Code`, `Code/...`), its build
output, its `native_decide` trust ledger, and its line numbers describe the
standalone package, **not** this repository: `Code` no longer exists here, the
twelve compiler-evaluated witnesses are no longer theorems, and the line
numbers are those of the development repository, whose sources carry no
license header. Use the root integration section above for anything about the
current tree. The old build configuration is saved under
`sources/standalone-build-4.33.1/`; the original development commit provides
the complete historical package.

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
  `Equivalence/Minrun.lean:116`
- `CPythonListsort.minrunInit_eq_spec` —
  `Equivalence/Minrun.lean:134`
- `CPythonListsort.cIntMinrunMask_toNat_lt_pow` —
  `Equivalence/Minrun.lean:177`
- `CPythonListsort.minrunNext_eq_spec` —
  `Equivalence/Minrun.lean:194`
- `CPythonListsort.minrunInit_stops_and_exponent_lt_64` —
  `Equivalence/MinrunResults.lean:105`
- `CPythonListsort.minrunInit_modulus_le_listSize` —
  `Equivalence/MinrunResults.lean:135`
- `CPythonListsort.minrunInit_mask_lt_modulus` —
  `Equivalence/MinrunResults.lean:163`
- `CPythonListsort.minrunNextN_output_bounds` —
  `Equivalence/MinrunResults.lean:306`
- `CPythonListsort.minrunNext_after_init_bounds` —
  `Equivalence/MinrunResults.lean:320`
- `CPythonListsort.minrunNextN_eq_spec` —
  `Equivalence/MinrunResults.lean:416`
- `CPythonListsort.minrunPrefixSum` —
  `Equivalence/MinrunResults.lean:481`
- `CPythonListsort.minrunSequence` —
  `Equivalence/MinrunResults.lean:654`

The truncation regression is separately kernel-checked with ordinary
`decide`:

```text
'CPythonListsort.minrun_cIntMask_truncation_regression'
depends on axioms: [propext, Quot.sound]
```

Its declaration is at `Equivalence/MinrunResults.lean:353`. It proves
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

## Native trust ledger (historical)

```console
$ python3 verify/verify_trust_boundary.py
verified native_decide trust boundary: 12 named compiler-checked regressions, no Lean consumers
```

The twelve allowlisted proof leaves were:

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
because it uses kernel `decide`, not `native_decide`. In the integrated tree
the twelve entries above are asserting `IO Unit` regressions under
`CSLibExtTest.Algorithms.Sorting.CPythonListsort`, and the verifier's current
message differs accordingly.

## Pinned-source verification

This check requires network access to the pinned CPython commit:

```console
$ python3 verify/verify_excerpts.py
verified sources/listobject-excerpts.md
verified sources/listsort.md
```

The reviewed transcription uses the 32-bit mask operation at
`Transcription/Minrun.lean:57`. Exact quotient/remainder results carry
the explicit `mr_e < 32` premise, while the top-level scan consumes the
unconditional arbitrary-call band through
`Assembly/ListSortSupport.lean:261`.

## Verdict

**PASS (standalone, 4.33.1).** The export of development commit `7a5f47d`
builds completely, has no proof gaps, preserves the two-tier trust boundary,
restricts exact minrun equivalence honestly, and includes a kernel-checked
proof of `1 ≤ minrun ≤ 64` for every reachable call count. This verdict is
about the standalone package; the root-toolchain verdict is in the root
integration section above.
