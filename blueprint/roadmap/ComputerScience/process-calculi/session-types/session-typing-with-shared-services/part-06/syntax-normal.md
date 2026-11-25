# Runtime-typed processes are congruent to a guarded normal form

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context and $p$ a
process with $\Gamma; \Delta \vdash_n p$ (runtime typing with shared services). Then there is a
process $q$ in guarded normal form for $\Gamma$ (a parallel composition of service templates and
prefixed processes under zero or more restrictions) with $p \equiv q$.
