# Bit-level equivalence

This chapter connects the reviewed finite-width implementation definitions to
clear mathematical specifications. It may use arithmetic and bit-vector
lemmas, but it never substitutes a cleaner algorithm for the transcription.

The conditional recurrence equivalence for `powerloop` and the adaptive-minrun
bridges are formalized. Adaptive minrun deliberately has two contracts: exact
quotient/remainder and balanced-cycle equivalence while `mr_e < 32`, and an
independent output-band theorem for every admitted input and every reachable
call count. The top-level safety and correctness chains consume the latter,
so they do not assume that C's 32-bit mask is the arbitrary-precision mask in
the design-note generator; the direct assembly application is
`adaptiveMinrun_step_facts` at
`Code/Assembly/ListSortSupport.lean:270`.

## Power computation

- [Natural-number `powerloop` specification](powerloop-nat-spec.md)
- [`powerloop` safety-trace specification](powerloop-trace-spec.md)
- [`powerloop` recurrence equivalence](powerloop-equivalence.md)
- [`powerloop` input arithmetic bounds](powerloop-input-bounds.md)
- [Natural quotient-bit recurrence result](powerloop-nat-result.md)
- [`powerloop` trace safety](powerloop-trace-safety.md)
- [`powerloop` terminating-result characterization](powerloop-result.md)

## Adaptive minrun

- [`merge_init` exponent and conditional mask equivalence](minrun-init-equivalence.md)
- [`merge_init` exponent characterization](minrun-exponent-characterization.md)
- [Unconditional adaptive-minrun output band](minrun-output-range.md)
- [`minrun_next` conditional quotient-remainder equivalence](minrun-next-equivalence.md)
- [Adaptive-minrun prefix-sum invariant](minrun-prefix-sum.md)
- [Balanced adaptive-minrun sequence](minrun-sequence.md)
