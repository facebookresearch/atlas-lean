# The W-method gives complete test suites

Use deterministic, completely specified Mealy machines over fixed input and output alphabets, with equivalence of
states as in [characterization sets of finite-state machines](characterization-sets-of-minimal-finite-state.md).
Two machines are *equivalent* if their initial states produce the same output word on every input word, and they
*agree on* a set $T$ of input words if their initial states produce the same output word on every $w \in T$. A test suite $T$
is *$m$-complete* for $M$ if every machine with at most $m$ states that agrees with $M$ on $T$ is equivalent to $M$.

Let $M$ be minimal with $n$ states, let $P$ be a *state cover* of $M$ (a finite set of input words containing the empty
word and an access word for every state), let $W$ be a characterization set of $M$, and let $m \ge n$. Then the W test
suite

$$T = P \cdot I^{\le m - n + 1} \cdot W,$$

where $I^{\le k}$ is the set of input words of length at most $k$, is $m$-complete for $M$.

## Depends on

- [Characterization sets of finite-state machines](characterization-sets-of-minimal-finite-state.md)

## Sources

- B. Kocsis and J. Rot, "Complete test suites for automata in monoidal closed categories", arXiv:2411.13412v2: Definitions 2.2–2.4, Lemmas 2.5–2.6 and Corollary 2.7 (the W test suite $P \cdot \Sigma^{\le k+1} \cdot W$ is $(n+k)$-complete), and Section 5.1 (the Mealy-machine instance and agreement on whole output words).
- T. S. Chow, "Testing software design modeled by finite-state machines", *IEEE Transactions on Software Engineering* SE-4(3):178–187, 1978.
- M. P. Vasilevskii, "Failure diagnosis of automata", *Cybernetics* 9(4):653–665, 1973.
