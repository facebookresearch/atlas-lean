# Reed–Solomon folding over multiplicative cosets

Let $\mathbb{F}$ be a finite field, $\omega$ a primitive $aN$-th root of unity and $D = g\langle\omega\rangle$ a multiplicative coset of size $aN$; its $a$-th powers form a coset $D^a$ of size $N$, and $D$ splits into $N$ fibers $\{y\omega^{jN}\}_{j < a}$ above each $y^a \in D^a$. For a word $f : D \to \mathbb{F}$, the *fold* of $f$ with challenge $z$ is the word $\mathrm{Fold}(f, z) : D^a \to \mathbb{F}$,

$$
\mathrm{Fold}(f, z)(y^a) = \sum_{r=0}^{a-1} z^r f_r(y^a),
$$

where $f_0, \dots, f_{a-1}$ are the inverse-DFT components of $f$ on each fiber, i.e. the unique polynomials with $f(X) = \sum_r X^r f_r(X^a)$ on $D$. If $f$ is a Reed–Solomon codeword of dimension $ak$ on $D$, then $\mathrm{Fold}(f, z)$ is a Reed–Solomon codeword of dimension $k$ on $D^a$, for every $z$; and $f$ is recovered fiberwise from its $a$ components.

## Depends on

- [Reed-Solomon code](../../../../../InformationTheory/error-correcting-codes/reed-solomon-codes/code.md)

## Sources

- Eli Ben-Sasson, Iddo Bentov, Yinon Horesh and Michael Riabzev, "Fast Reed–Solomon Interactive Oracle Proofs of Proximity", 45th International Colloquium on Automata, Languages, and Programming (ICALP 2018), 2018.
