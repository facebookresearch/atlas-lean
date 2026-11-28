# The C11 and RC11 memory models

The axiomatic C11 concurrency model and its repair RC11 by Lahav, Vafeiadis, Kang, Hur and Dreyer: consistent executions and program outcomes, its relation to the C11 coherence and SC axioms, data-race freedom, SC fences, and sound compilation to x86-TSO.

- [The axiomatic C11 concurrency model](the-axiomatic-c11-concurrency-model.md)
- [RC11-consistent executions](rc11-consistent-executions.md)
- [RC11 without mixed SC accesses gives the C11 guarantee](rc11-without-mixed-sc-accesses-gives-the-c11-guarantee.md)
- [The RC11 SC condition as a total order on SC events](the-rc11-sc-condition-as-a-total-order.md)
- [RC11 coherence is equivalent to the C11 coherence axioms](coherence-in-rc11-is-equivalent-to-the-c11-coherence-axioms.md)
- [Outcomes of a program under RC11](rc11-program-outcomes.md)
- [Data-race freedom guarantees sequential consistency under RC11](drf-sc-for-rc11.md)
- [SC fences between shared accesses restore sequential consistency in RC11](sc-fences-restore-sequential-consistency-in-rc11.md)
- [Compilation of RC11 to x86-TSO is sound](compilation-of-rc11-to-x86-tso.md)
