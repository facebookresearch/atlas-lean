# Trace reconstruction on a tree under substitutions, insertions and deletions

**Model.** Let $T_{d,H}$ be the complete $d$-ary tree ($d$ odd) with $H$ levels and $n=d^H$ leaves. The root carries a uniformly random binary sequence $x=x_1\cdots x_k\in\{0,1\}^k$. Along each edge, every site independently is **substituted** (flipped) with probability $p_s$, **deleted** with probability $p_d$, and followed by an **inserted** uniform random site with probability $p_i$. These events are independent across sites and edges. Only the leaf sequences $Y_1,\dots,Y_n$ are observed, with no alignment. Write $\theta=1-2p_s$ and $p_{id}=p_i+p_d$. The **trace reconstruction problem on a tree** asks to recover $x$ from $Y_1,\dots,Y_n$.

**Theorem.** For every $\chi>0$ and $\beta=O(d^{-1}\log d)$ there are constants $\Phi,\Phi',\Phi''>0$ such that, for $d$ large enough, a polynomial-time algorithm with access to $Y_1,\dots,Y_n$ achieves the following whenever

$$\theta^2=(1-2p_s)^2>\frac{\Phi\log d}{d},\qquad p_i+p_d<\frac{\Phi'}{k^{2/3}\log n},\qquad \Phi''\log^3n<k<\operatorname{poly}(n).$$

With probability at least $1-\chi$ it outputs a sequence $\hat x=\hat x_1\cdots\hat x_k$ of length exactly $k$ with $\mathbb P(\hat x_j=x_j)>1-\beta$ for every $j=1,\dots,k$. It also produces an alignment of the leaf sequences.

## Expansion

Without indels this is ancestral reconstruction for the binary symmetric channel on a tree: recursive majority recovers the root symbol with probability bounded away from $\tfrac12$ uniformly in depth exactly above the Kesten–Stigum-type threshold $d\theta^2>1$, up to the $\log d$ factor here. Indels destroy the positional correspondence between sites. The algorithm restores it locally by cutting sequences into islands of length $k^{1/3}$ separated by short anchors. At each internal node it aligns the children's reconstructed sequences anchor by anchor, discards *radioactive* nodes in which an indel hit an anchor or misaligned an island, and applies recursive majority site by site to the aligned islands. The indel rate $p_{id}\ll k^{-2/3}/\log n$ makes radioactive nodes rare enough that the majority vote among the $d$ children still corrects them, and the error stays $O(d^{-1}\log d)$ per site at every level. The result serves as a bootstrapping step toward information-theoretically optimal phylogeny reconstruction under indel models.

## Sources

- Alexandr Andoni, Constantinos Daskalakis, Avinatan Hassidim, Sebastien Roch, "Global Alignment of Molecular Sequences via Ancestral State Reconstruction", arXiv:0912.2577 (2009), Definition 1.1 (model of sequence evolution), Theorem 1.3 (main result) and Section 3 (indel structure and recursive reconstruction), <https://doi.org/10.48550/arXiv.0912.2577>.
