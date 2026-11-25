# Choice selection is the identity on runtime-typed processes

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context and $p$,
$q$ processes with $\Gamma; \Delta \vdash_n p$. If $q$ is obtained from $p$ by guarded-choice
resolution (repeatedly replacing a top-level choice by one of its branches), then $q = p$.
