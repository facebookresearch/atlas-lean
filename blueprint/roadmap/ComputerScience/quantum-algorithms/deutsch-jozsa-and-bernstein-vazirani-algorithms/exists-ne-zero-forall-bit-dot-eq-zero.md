# Classical evaluations: fewer than $n$ never determine $s$

For every set $Q \subseteq \mathbb{Z}_2^n$ of fewer than $n$ points there is $u \neq 0$ with $u\cdot x = 0$
for all $x \in Q$ (the linear map $u \mapsto (u\cdot x)_{x\in Q}$ has a nontrivial kernel). Hence
$x \mapsto s\cdot x$ and $x \mapsto (s+u)\cdot x$ agree on $Q$, and evaluations at the points of $Q$
cannot tell $s$ from $s + u$.

This is the counting fact behind the remark of Bernstein and Vazirani (Section 8.4, after
Theorem 8.4.2) and Cleve, Ekert, Macchiavello and Mosca (after equation (3.7)) that a classical algorithm
needs $n$ evaluations. For an adaptive deterministic algorithm, apply it to the points the algorithm
queries when every answer is $0$ (the case $s = 0$): the algorithm then behaves identically for
$s = 0$ and $s = u$.

## Sources

- E. Bernstein and U. Vazirani, "Quantum complexity theory", SIAM Journal on Computing 26 (1997), 1411–1473; author-hosted version dated September 8, 1997 (https://people.eecs.berkeley.edu/~vazirani/pubs/bv.pdf), Section 8.4. Theorem numbers on this page refer to that version.
- R. Cleve, A. Ekert, C. Macchiavello and M. Mosca, "Quantum algorithms revisited", Proceedings of the Royal Society of London A 454 (1998), 339–354; arXiv:quant-ph/9708016v1, Section 3, equations (3.1)–(3.9).
