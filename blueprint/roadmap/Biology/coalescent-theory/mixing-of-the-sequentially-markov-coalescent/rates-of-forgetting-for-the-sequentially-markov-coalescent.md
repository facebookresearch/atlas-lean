# Rates of forgetting for the sequentially Markov coalescent

**SMC (pairwise).** Let $(Y_\ell)_{\ell\ge0}$ be the pairwise TMRCA along the chromosome in coalescent time units, with genetic distance $\ell$ scaled so that recombination on a tree of height $y$ occurs at rate $y$. It is the Markov jump process that, in state $y$, waits an $\mathrm{Exp}(y)$ distance and jumps to $Uy+Z$ with $U\sim\mathrm{Unif}(0,1)$ (recombination point on the tree) and $Z\sim\mathrm{Exp}(1)$ (re-coalescence time above it). Its jump chain has density
$$q_{\mathrm{SMC}}(t\mid s)=\frac{e^{-t}\,(e^{s\wedge t}-1)}{s},$$
reversible for $\mu(dt)=te^{-t}dt$, while the continuous process has the stationary law $\pi=\mathrm{Exp}(1)$ (the Kingman pairwise TMRCA).

**SMC'.** Recombination still occurs at rate $y$, but the detached lineage may re-coalesce with its own lineage, which makes the event silent. A recombination is visible with probability $p_{\mathrm{vis}}(s)=\frac{2s+1-e^{-2s}}{4s}$, and the jump chain density is $q_{\mathrm{SMC}'}(t\mid s)=\frac{2(1-e^{-2t})}{2s+1-e^{-2s}}$ for $t<s$ and $\frac{2(1-e^{-2s})}{2s+1-e^{-2s}}e^{-(t-s)}$ for $t\ge s$, reversible for $\mu'(dt)=\frac38(2t+1-e^{-2t})e^{-t}dt$.

**Theorem (jump chains).** For every starting state $x>0$ and $n\ge1$,
$$d_{\mathrm{TV}}\big(K^n_{\mathrm{SMC}}(x,\cdot),\mu\big)\le\frac{\tfrac52(x+2)}{2^n},\qquad d_{\mathrm{TV}}\big(K^n_{\mathrm{SMC}'}(x,\cdot),\mu'\big)\le\frac{x+\tfrac{11}6}{2^{n-1}} .$$

**Theorem (continuous processes).** The SMC transition kernel is $P_\ell(x,dy)=e^{-\ell x}\delta_x(dy)+p_\ell(x,y)dy$ with $p_\ell(x,y)=\frac{\ell}{\ell-1}e^{-y}\big(1-e^{-(\ell-1)\min(x,y)}\big)$ ($\ell\ne1$), and for fixed $x$ there is $\ell_0(x)$ with
$$\frac1{2\ell}\le d_{\mathrm{TV}}\big(P_\ell(x,\cdot),\pi\big)\le\frac1\ell\qquad(\ell\ge\ell_0(x)).$$
The SMC' process is a time change of the SMC: with $N_\ell$ a rate-$\tfrac14$ Poisson process independent of $Y$, $Y'_\ell\stackrel d=Y_{C_\ell}$, $C_\ell=\ell/2+2N_\ell$; consequently $d_{\mathrm{TV}}(P'_\ell(x,\cdot),\pi)\asymp1/\ell$ as well. By data processing, the same upper bounds control the pairwise TMRCA marginals of an $n$-sample genealogy.

## Expansion

The jump chains contract because each jump keeps only a uniform fraction of the current height: the mean map $m(s)=\int t\,q(t\mid s)dt$ is a contraction with ratio $1/2$, so a monotone quantile coupling brings two copies together geometrically, and an $L^1$-Lipschitz bound on $s\mapsto q(\cdot\mid s)$ converts closeness into total variation. The continuous process is slow for a different reason: at small heights the jump rate $y$ is small, so starting from $x$ the probability of no jump by distance $\ell$ is $e^{-\ell x}$, and averaging the time spent in low states makes the distance to stationarity decay only polynomially. The Laplace transform $\mathbb E_xe^{-\lambda Y_\ell}=1-\frac{\lambda(1+\lambda+\ell)}{(1+\lambda)(\lambda+\ell)}(1-e^{-(\lambda+\ell)x})$ yields the explicit kernel and the matching $1/(2\ell)$ lower bound. Practically, loci at genetic distance $\ell$ are approximately independent only up to an $O(1/\ell)$ error, which quantifies heuristics that treat distant loci as independent in SMC-based inference.

## Sources

- J. Terhorst, "Rates of forgetting for the sequentially Markov coalescent", arXiv:2604.20629 (2026), Section 2 (Definitions 1-2, Proposition 3), Section 3 (Proposition 4, Lemmas 5-6, Theorems 7, 8, 10, 11, 12, Proposition 9, Remark 13) and Appendix A (Theorem 14), <https://doi.org/10.48550/arXiv.2604.20629>.
