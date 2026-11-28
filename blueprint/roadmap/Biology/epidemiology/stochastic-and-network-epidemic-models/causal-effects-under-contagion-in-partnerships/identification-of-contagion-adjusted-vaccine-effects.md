# Identification of contagion-adjusted vaccine effects

**Setting.** In a partnership $\{i,j\}$ with binary treatments $\mathbf{x}=(x_i,x_j)$ and covariates $\mathbf{L}$, let $W_i(\mathbf{x})$ be the potential time to infection of $i$ from outside the partnership, and $Z_i(w_j,\mathbf{x})$ the additional potential time to infection of $i$ after $j$ is infected at time $w_j$. The observed infection time is $T_i=W_i$ if $W_i<W_j$ and $T_i=W_j+Z_i$ otherwise, and $Y_i(t)=\mathbf{1}\{T_i\le t\}$. $Y_i(t;w_j,\mathbf{x})$ denotes the potential outcome when $j$'s infection time is set to $w_j$.

**Assumptions.** (1) Exclusion and independence: $W_i(\mathbf{x})=W_i(x_i)$, $W_i(x_i)\perp W_j(x_j)\mid\mathbf{L}$, $W_i(x_i)\perp\mathbf{L}_j\mid\mathbf{L}_i$. (2) $Z_i(w_j,\mathbf{x})\perp W_j(x_j)\mid\mathbf{L}$. (3) Treatment exchangeability given $\mathbf{L}$. (4) Consistency. (5) Positivity.

**Theorem.** Under (1)–(5), the distribution of $W_i(x_i)$ given $\mathbf{L}_i$ is identified by the cause-specific hazard

$$F_i(w\mid x_i,\mathbf{l}_i)=1-\exp\Bigl[-\int_0^w\frac{p(T_i=u,T_j>u\mid\mathbf{X}=\mathbf{x},\mathbf{L}=\mathbf{l})}{\Pr(T_i>u,T_j>u\mid\mathbf{X}=\mathbf{x},\mathbf{L}=\mathbf{l})}\,du\Bigr]$$

(for any fixed $x_j,\mathbf{l}_j$), and for $w_j<t$

$$\mathbb{E}[Y_i(t;w_j,\mathbf{x})\mid\mathbf{L}=\mathbf{l}]=F_i(w_j\mid x_i,\mathbf{l}_i)+\bigl(1-F_i(w_j\mid x_i,\mathbf{l}_i)\bigr)\,\mathbb{E}[Y_i(t)\mid T_i\ge w_j,T_j=w_j,\mathbf{X}=\mathbf{x},\mathbf{L}=\mathbf{l}],$$

while for $t\le w_j$ it equals $F_i(t\mid x_i,\mathbf{l}_i)$. Natural outcomes are identified by $\mathbb{E}[Y_i(t;W_j(x_j),\mathbf{x})\mid\mathbf{L}]=\mathbb{E}[Y_i(t)\mid\mathbf{X}=\mathbf{x},\mathbf{L}]$, and, under an extra cross-world assumption, by integrating the controlled outcome against $dF_j(w_j\mid x_j',\mathbf{l}_j)$.

**Estimands.** Controlled *contagion* effect $\mathrm{CE}(t,w_j,w_j',\mathbf{x})=\mathbb{E}[Y_i(t;w_j,\mathbf{x})-Y_i(t;w_j',\mathbf{x})]$; *susceptibility* effect $\mathrm{SE}(t,w_j,x_j)$, changing $x_i$ with $w_j$ fixed; *infectiousness* effect $\mathrm{IE}(t,w_j,x_i)$, changing $x_j$ with $w_j$ fixed.

**Sign results.** Suppose treatment has no susceptibility effect but reduces infectiousness ($\mathrm{SE}=0$, $\mathrm{IE}<0$). If partners' treatments are positively dependent, the direct effect satisfies $\mathrm{DE}(t)<0$ and the attack-rate efficacy $\mathrm{VE}_{\mathrm{AR}}(t)=1-\mathrm{AR}_1(t)/\mathrm{AR}_0(t)>0$; if negatively dependent, $\mathrm{DE}(t)>0$ and $\mathrm{VE}_{\mathrm{AR}}(t)<0$; if independent, both are $0$. So attack-rate comparisons can show a spurious susceptibility effect. With no treatment effect at all, both vanish for any treatment distribution. When the treated partner cannot be infected from outside ($h_0^i(t\mid0)=0$), the conventional infectiousness efficacy $\mathrm{VE}_I(t)$ equals the infectiousness effect $\mathrm{IE}(t,0)$.

## Expansion

Before either partner is infected both are exposed only to the community, so the first-infection hazard of $i$ while both are uninfected identifies the law of $W_i$ (a competing-risks argument made valid by the independence in (1)). After $j$'s infection at $w_j$, exchangeability (2) makes the residual time $Z_i$ independent of when $j$ was infected, so the observed conditional outcome given $T_j=w_j$ and $T_i\ge w_j$ identifies the post-exposure part. Combining the two pieces gives the formula. Contagion is a causal phenomenon that creates conditional independences among infection outcomes, and these are what make the estimands identifiable from time-to-infection data.

## Sources

- X. Cai, W. W. Loh, F. W. Crawford, "Identification of causal intervention effects under contagion", arXiv:1912.04151 (2019), Assumptions 1–6, Lemma 1, Theorem 1, Corollary 1, Definitions 1–3, Theorems 2–5, <https://doi.org/10.48550/arXiv.1912.04151>.
