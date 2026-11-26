# Macrorates of a ligand-coupled RNA folding landscape

**Setting.** Let $X=\{R_1,\dots,R_N\}$ be the secondary structures (monomer microstates) of an RNA with free energies $E(x)$, and let $X^+\subseteq X$ be the structures that contain a ligand binding pocket. The dimer microstates are $X^*=\{Lx : x\in X^+\}$ with energy $E(Lx)=E(x)+\theta$, where $\theta<0$ is the RNA–ligand binding energy. Write $\mathfrak b=1/(RT)$, $Z[S]=\sum_{x\in S}e^{-\mathfrak b E(x)}$ for the partition function of a set $S$ of microstates, and $\Pr[x\mid S]=e^{-\mathfrak b E(x)}/Z[S]$ for $x\in S$ (and $0$ otherwise).

Two microstates are neighbours ($x\mathcal N y$) if they differ by one elementary move (insertion or deletion of a base pair, or binding/unbinding of the ligand). Microrates follow the Metropolis rule

$$k(x\to y)=A(x\to y)\exp\!\big(-\mathfrak b\,[\max\{E(x),E(y)\}-E(x)]\big)\quad (x\mathcal N y),\qquad k(x\to y)=0 \text{ otherwise},$$

with pre-exponential factor $A_R$ for conformational moves (equal in monomers and dimers), $A_a$ for association and $A_d$ for dissociation. For macrostates (sets of microstates) $\alpha,\beta$ the macrorate is

$$r(\alpha\to\beta)=\sum_{x\in\alpha,\;y\in\beta}\Pr[x\mid\alpha]\,k(x\to y).$$

**Lemma 1 (dimer landscape copies the monomer landscape).** For $x,y\in X^+$, $k(Lx\to Ly)=k(x\to y)$; for every $\alpha\subseteq X^+$, $\Pr[Lx\mid L\alpha]=\Pr[x\mid\alpha]$; hence $r(L\alpha\to L\beta)=r(\alpha\to\beta)$ for all $\alpha,\beta\subseteq X^+$. In particular rates inside the dimer landscape do not depend on $\theta$.

**Lemma 2 (association and dissociation microrates).** For $x\in X^+$, $k(x\to Lx)=A_a$ and $k(Lx\to x)=A_d\,e^{\mathfrak b\theta}$; all other monomer–dimer microrates vanish.

**Lemma 3 (association and dissociation macrorates).** For any $\alpha\subseteq X$ and $\beta\subseteq X^+$,

$$r(\alpha\to L\beta)=A_a\,\frac{Z[\alpha\cap\beta]}{Z[\alpha]},\qquad r(L\beta\to\alpha)=A_d\,\frac{Z[\alpha\cap\beta]}{Z[\beta]}\,e^{\mathfrak b\theta}.$$

## Expansion

Shifting every dimer energy by the same constant $\theta$ leaves energy differences between dimer neighbours unchanged, so Metropolis activation energies and conditional Boltzmann weights inside $L\alpha$ are those of $\alpha$; summing gives Lemma 1. Since $\theta<0$, binding is downhill and its activation energy is zero ($k=A_a$), while unbinding climbs by $-\theta$ ($k=A_d e^{\mathfrak b\theta}$), which is Lemma 2. In Lemma 3 only pairs $(x,Lx)$ with $x\in\alpha\cap\beta$ contribute, and summing their Boltzmann weights produces the partition-function ratios. Detailed balance between $x$ and $Lx$ forces $A_a=A_d$ in this parametrisation. Practically, gradient-basin coarse graining of the pocket-constrained landscape can be computed once and reused for every binding energy.

## Sources

- Kühnl F, Stadler PF, Will S, "Tractable RNA-ligand interaction kinetics" (2017), Lemma 1, Lemma 2 and Lemma 3 (Results, "Macrostate kinetics of RNA–ligand interaction"), <https://doi.org/10.1186/s12859-017-1823-5>, PMCID PMC5657077.
