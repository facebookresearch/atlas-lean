# Asymptotic normality of motif counts under the Knudsen–Hein RNA grammar

**Model.** The Knudsen–Hein stochastic context-free grammar (used by the Pfold RNA structure predictor) generates secondary structures by the rules

$$S\to LS\ (p_1)\mid L\ (q_1),\qquad L\to dFd'\ (p_2)\mid s\ (q_2),\qquad F\to dFd'\ (p_3)\mid LS\ (q_3),$$

with $p_i+q_i=1$. Here $s$ is an unpaired base and $d\,d'$ a base pair. The probability generating functions in the number $n$ of nucleotides satisfy $S=p_1LS+q_1L$, $L=p_2z^2F+q_2z$ and $F=p_3z^2F+q_3LS$, so

$$p_2q_3z^2S(z)^2-(1-p_1q_2z)(1-p_3z^2)S(z)+q_1q_2z(1-p_3z^2)=0 .$$

The grammar is consistent ($S(1)=1$) iff $(1+q_1)q_2\ge1$. The dominant singularity of $S$ is a square-root branch point $\rho_0$ with $1<\rho_0<\min\{1/(p_1q_2),1/\sqrt{p_3}\}$.

**Theorem.** Let $\mathbb X_n$ count, in a random structure with $n$ nucleotides drawn from the grammar, the base pairs, the helices, or the loops of a fixed type (hairpin, bulge, interior, multiloop). For all probability parameters outside a measure-zero set, given by a nondegeneracy condition $f(p_1,p_2,p_3)\ne0$, there are constants $\mu,\sigma>0$ with

$$\sup_{x\in\mathbb R}\Big|\mathbb P\Big(\frac{\mathbb X_n-\mu n}{\sqrt{\sigma^2n}}<x\Big)-\Phi(x)\Big|=O(n^{-1/2}).$$

For base pairs, $\mathbb E\mathbb X^{bp}_n\sim\frac{\alpha}{\gamma}n$ with $\alpha=1-p_1q_2\rho_0$ and $\gamma=3-p_1q_2\rho_0-p_3\rho_0^2-p_1p_3q_2\rho_0^3$. Independently of the parameters, the expected motif counts satisfy, to leading order in $n$:

- left and right bulges have equal means;
- multiloops are one quarter of helices;
- hairpins equal interior loops plus multiloops;
- multiloops equal left bulges plus interior loops;
- multiloops with $r+1$ branches number fewer than half of those with $r\ge2$ branches.

## Expansion

Marking a motif by a variable $u$ turns the grammar equations into an algebraic system for $S(z,u)$, and the dominant singularity $\rho(u)$ moves analytically with $u$ near $u=1$. The quasi-powers theorem (Hwang; Flajolet–Sedgewick) then gives a Gaussian limit with mean $\mu n$, $\mu=-\rho'(1)/\rho(1)$, and linear variance, provided the variability condition $\sigma^2\ne0$ holds. That condition is the polynomial $f$, which vanishes only on a null set. The parameter-free relations come from the structure of the grammar: every helix ends in exactly one loop, and the loop types are determined by how $F\to LS$ unfolds. As a result, some ratios are rigid regardless of how the probabilities are trained. Comparing these predictions with ribosomal RNA structures shows which motif frequencies the model cannot reproduce, such as the fixed multiloop-to-helix ratio.

## Sources

- Svetlana Poznanovik, Christine E. Heitsch, "Asymptotic distribution of motifs in a stochastic context-free grammar model of RNA folding", arXiv:1204.3670 (2012), Section 2 (grammar and generating functions), Theorem 2.2, Corollary (parameter-free relations), Lemma 3.2, Theorems 4.2–4.3, <https://doi.org/10.48550/arXiv.1204.3670>.
