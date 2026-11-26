# Polynomial Time

Four fixed finite-state Turing machines must realize the actual distributions of key generation, encryption and public evaluation and the deterministic decryption result on the specified bit encodings. A randomized machine receives a uniform bit tape; its output distribution must agree exactly, and the step bound must hold on every tape.

The family index specifies either no level or a positive level $d$. Put $k=\lambda$ with no level and $k=\lambda+d$ otherwise. One pair of polynomials $q,p$ bounds the computation uniformly: the random tape has $q(k)$ bits and the machine takes at most $p(k)$ steps. Only for evaluation replace $k$ by $k+t+g$, where $t$ is the number of circuit inputs and $g$ the number of gates. The machine receives the circuit's actual [description](circuit-code.md); a longer spelling of a gate name buys no extra steps. With no level, every circuit is admitted; at level $d$, circuits of depth at most $d$ are admitted.
