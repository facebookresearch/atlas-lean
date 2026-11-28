# Maximum-entropy base-pair queries on a Boltzmann structure ensemble

**Setting.** Let $\Omega$ be a (sampled) Boltzmann ensemble of secondary structures of an RNA sequence, each structure $s$ having probability $p(s)$. Its *structural entropy* is $H(\Omega)=-\sum_{s\in\Omega}p(s)\log_2p(s)$. A *bit query* asks whether a base pair $(i,j)$ is present; it is the Bernoulli random variable $X_{i,j}(s)=\mathbf 1[(i,j)\in s]$ with $\mathbb{P}(X_{i,j}=1)=p_{i,j}$, the base-pairing probability. It splits $\Omega$ into $\Omega_0^{i,j}$ and $\Omega_1^{i,j}$, the *conditional entropy* is $H(\Omega\mid X_{i,j})=(1-p_{i,j})H(\Omega_0)+p_{i,j}H(\Omega_1)$ (with renormalized distributions on each block), and the *entropy reduction* is $R(\Omega,X_{i,j})=H(\Omega)-H(\Omega\mid X_{i,j})$.

**Proposition (distinguished structure).** If a sample has structural entropy $E\in[0,1]$, it contains a structure of probability at least $f(E)$, where $f(E)\in[1/2,1]$ solves $-p\log_2p-(1-p)\log_2(1-p)=E$. For example $f(1)=0.5$, $f(0.469)\approx0.9$, $f(0.286)\approx0.95$.

**Proposition (entropy reduction).** For every base pair,

$$
R(\Omega,X_{i,j})=H(X_{i,j})=-p_{i,j}\log_2p_{i,j}-(1-p_{i,j})\log_2(1-p_{i,j}).
$$

**Proposition (maximum-entropy query is optimal).** If $(i_0,j_0)$ maximizes $H(X_{i,j})$, then for every $(i,j)$:

$$
\big|\mathbb{P}(\Omega_0^{i_0,j_0})-\mathbb{P}(\Omega_1^{i_0,j_0})\big|\le\big|\mathbb{P}(\Omega_0^{i,j})-\mathbb{P}(\Omega_1^{i,j})\big|,\qquad R(\Omega,X_{i_0,j_0})\ge R(\Omega,X_{i,j}).
$$

## Expansion

Because $X_{i,j}$ is a function of the structure, $H(\Omega)=H(\Omega,X_{i,j})=H(X_{i,j})+H(\Omega\mid X_{i,j})$ by the chain rule, which gives the entropy-reduction identity. Binary entropy is symmetric about $1/2$ and increasing in $\min(p,1-p)$, so the maximum-entropy pair is the one with $p_{i,j}$ closest to $1/2$, giving the most balanced split and the largest reduction. Iterating such queries builds an *ensemble tree* whose leaves have low entropy; by the first proposition, once entropy drops below about $0.47$ bits a single structure carries 90% of the mass. In practice the answers come from chemical probing data, which is how the framework improves target identification from probing.

## Depends on

- [Base-pair probability](../../mccaskill-partition-function-for-rna-folding/pair-prob.md)

## Proof depends on

- [Chain rule for entropy](../../../../InformationTheory/entropy-and-mutual-information/conditional-entropy-and-mutual-information/shannon-entropy-eq-add-finite-conditiona.md)

## Sources

- Thomas J. X. Li, Christian M. Reidys, "On an enhancement of RNA probing data using Information Theory", arXiv:1909.05744: Section 2 (bit queries); Section 4 (the ensemble tree, Propositions 1–3); Appendices F–G (proofs). <https://doi.org/10.48550/arXiv.1909.05744>
