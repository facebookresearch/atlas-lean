# Compressing the relaxed verifier output with powers of a challenge

Let $\mathbf{v}=(v_1,\dots,v_\ell)\in\mathbb{F}^{\ell}$ be the vector output of an algebraic verifier and $\ell=\ell_1\ell_2$. For a random $\beta\in\mathbb{F}$, replacing the $\ell$ checks $v_i=0$ by the single check $\sum_{i=1}^{\ell}\beta^{i-1}v_i=0$ is sound except with probability $(\ell-1)/|\mathbb{F}|$. Moreover, writing $i-1=a\ell_1+b$ with $0\le b<\ell_1$, $0\le a<\ell_2$, one has $\beta^{i-1}=\beta^{b}\cdot(\beta^{\ell_1})^{a}$, so the prover can send the $\ell_1+\ell_2$ powers $\beta^{b}$ and $\beta'^{a}$ with $\beta'=\beta^{\ell_1}$ as part of its message, and the compressed check becomes a degree-$(d+2)$ algebraic check with a single field-element output; the consistency of the powers is itself a degree-$2$ algebraic relation.

## Proof sketch

If $\mathbf{v}\ne\mathbf{0}$, $p(Y)=\sum_i v_iY^{i-1}$ is a nonzero polynomial of degree at most $\ell-1$, so $\Pr_\beta[p(\beta)=0]\le(\ell-1)/|\mathbb{F}|$. The factorization of exponents is the division algorithm, and multiplying the degree-$d$ check by two power terms raises the degree by $2$.

## Depends on

- [Special-sound protocols with algebraic degree-d verifiers](special-sound-algebraic-verifier.md)

## Sources

- Benedikt Bünz, Binyi Chen, "Protostar: Generic Efficient Accumulation/Folding for Special-Sound Protocols", ASIACRYPT (2023), IACR ePrint 2023/620.
