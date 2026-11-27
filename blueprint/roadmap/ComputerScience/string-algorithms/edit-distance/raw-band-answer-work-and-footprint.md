# Answer, work, and footprint of the raw-band edit model

The exact and large branches use the fixed [branch guard and random law](raw-band-branch-and-randomness-model.md). Write $x,y$ for the recoded lists. The natural answer for an exact outcome or when the branch guard is false is `exactSuffixAnswer x y`. Otherwise project the large outcome to its accepted query input, construct the integer-symbol occurrence index and use the corresponding input-symbol and target-position bit sizes. For equal lists the binary answer word is empty (zero) and the answer counter is $|x|+|y|+1$. For unequal lists evaluate the normalized raw query in the ranked bit memo with empty initial dictionary, slot bound $16384H+5$ and `computedFamilyMemoCode` at refinement bound $H^2$. The initial request is the refinement request at pass `computedSeedPassCount N`, copy zero, root source path and terminal target interval, in the right summand of the memo key space (with $T=2^{\lfloor(3h+3)/4\rfloor}$ and $S=\lfloor H/\ell^2\rfloor$). Normalization uses `computedQueryBase N`, and a child query must have smaller `SourceRanked.rank` for `ChargedPhysicalRequest.rank`; the raw programs, normalization and physical key coding are those pinpointed below. Take the memo’s rational result, take its nonnegative natural floor, clamp it to $N$, and interpret the output as a little-endian word. The exact query-return work includes the floor/clamp work and $|x|+|y|+1$; do not replace the charged polynomial with the numeric value of the answer.

For each outcome the real work-counter value is the natural pre-evaluation tally (input preprocessing, global parameters, branch test), plus the following branch charge. On the exact tag charge `chargedSuffixDP` work and $N+1$. On the large tag charge the work component of `computedQuerySetupWithWork`, and `computedExecutionTotalWork` plus the work component of `integerBinaryOutputRawBand` at the accepted input. Total execution work is the sum of indexed coarse work, coarse sampling work, nonlocal work, coarse preparation work, and the ranked-family kernel work on the normalized query’s per-key local-work function. In particular the law and the work retain the rejection arrays; exact arithmetic procedures, dictionary visits and normalization are charged by the cited counters, not by an unspecified unit-cost RAM.

The space function returns, for a false guard or exact tag, $8$ times pre-evaluation work plus $2$ times `integerStoredDataSpace` plus `suffixDPAllocation` plus $8(N+1)$. For a true guard and large tag it sums: $8$ times pre-evaluation, $2$ times stored-data space, setup allocation, fraction storage of the actual ranked memo result, temporary cells measured by the separate normalized footprint query `computedQueryTemporaryCellsFootprintRawBand`, coarse copy storage, coarse array, scratch and control capacities, $4(H+B+4)$, final allocation, and $8(N+1)$. These are the semantic counters of the linked model, including the per-key encoders and allocation counters. In particular this is not worst-case running time, resident memory of an arbitrary implementation, or memory averaged over the law.

## Depends on

- [Indexed product law, guard and accepted input](raw-band-branch-and-randomness-model.md)
- Ranked memo request/value and the exact bit-operation and allocation counters, fixed by the pinned definitions below.

## Expansion

Make the indexed read law, normalization and per-key resource counters native before transferring any bound. Compare fallback and accepted outcomes separately. The linked proof reuses agreement lemmas for the outputs and both counters, not an unproved equality to a different machine’s cost.

## Sources

- [Exact charged suffix dynamic programming](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L746-L788)
- [Nonnegative binary floor and cap conversion](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L1617-L1633)
- [Exact answer for the fallback](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L3029-L3042)
- [Pre-evaluation cost tally](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L13744-L13761)
- [Accepted projection, final root and kernel-work function](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L15197-L15224)
- [Execution read charges, total work and branch charges](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L15477-L15525)
- [Raw-family memo and normalized typed query](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L17474-L17535)
- [Normalization, empty-dictionary evaluation and binary output](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L17548-L17629)
- [Integer answer and branch selection](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L17636-L17677)
- [Raw-band work and final allocation](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L18167-L18204)
- [Normalized raw-band space counter and branch footprints](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L19010-L19145)
- [Proof via exact answer/work/footprint agreement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/EditApproximation/Specification/RawBandMain.lean#L1-L32)
