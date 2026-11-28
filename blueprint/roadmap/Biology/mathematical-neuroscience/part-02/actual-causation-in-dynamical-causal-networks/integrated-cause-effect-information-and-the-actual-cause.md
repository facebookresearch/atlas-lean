# Integrated cause-effect information and the actual cause of an occurrence

Work in a dynamical causal network with transition $v_{t-1}\prec v_t$ and cause/effect repertoires $\pi$ obtained by causal marginalization.

**Partitions.** A permissible partition of an occurrence $x_{t-1}$ together with the nodes $Y_t$ it constrains is either $\psi = \{(x_{1,t-1}, Y_{1,t}),\dots,(x_{m,t-1}, Y_{m,t})\}$ with $2 \le m \le \lvert x_{t-1}\rvert$, where the $x_{j,t-1}$ partition $x_{t-1}$ into nonempty parts and the $Y_{j,t}\subseteq Y_t$ are disjoint (possibly empty), or the single cut $\psi = \{(x_{t-1}, \varnothing)\}$. For cause repertoires the roles are exchanged: $2 \le m \le \lvert y_t\rvert$ parts of $y_t$, or the single cut $\{(\varnothing, y_t)\}$. The partitioned effect repertoire is

$$\pi(Y_t\mid x_{t-1})_\psi = \prod_{j=1}^m \pi(Y_{j,t}\mid x_{j,t-1})\times \pi\Big(Y_t\setminus \textstyle\bigcup_j Y_{j,t}\Big),$$

the last factor being the unconstrained repertoire; partitioned cause repertoires $\pi(X_{t-1}\mid y_t)_\psi$ are defined symmetrically.

**Integrated information.** With the minimum information partition (MIP) being the permissible partition that reduces $\rho$ least,

$$\alpha_e(x_{t-1}, y_t) = \log_2\frac{\pi(y_t\mid x_{t-1})}{\pi(y_t\mid x_{t-1})_{\mathrm{MIP}}},\qquad \alpha_c(x_{t-1}, y_t) = \log_2\frac{\pi(x_{t-1}\mid y_t)}{\pi(x_{t-1}\mid y_t)_{\mathrm{MIP}}}.$$

For a single-variable occurrence the only partition cuts it from its target, so $\alpha = \rho$.

**Irreducibility and actual causes.** Define

$$\alpha_e^{\max}(x_{t-1}) = \max_{y_t\subseteq v_t}\alpha_e(x_{t-1}, y_t),\qquad \alpha_c^{\max}(y_t) = \max_{x_{t-1}\subseteq v_{t-1}}\alpha_c(x_{t-1}, y_t),$$

including the empty set, so $\alpha^{\max}\ge 0$. If $\alpha^{\max} = 0$ the occurrence is reducible and has no actual cause or effect. Otherwise the **actual effect** of $x_{t-1}$ is a $y_t$ attaining $\alpha_e^{\max}(x_{t-1})$ that is minimal (no proper subset attains the same value), and the **actual cause** of $y_t$ is a minimal $x_{t-1}$ attaining $\alpha_c^{\max}(y_t)$. If several minimal maximisers exist the actual cause (or effect) is undetermined among them. The *causal account* of the transition is the set of all such causal links, in both directions, with strength $\alpha^{\max}$; a link $x_{t-1}\to y_t$ does not imply $x_{t-1}\leftarrow y_t$.

## Expansion

The five requirements are realization (only occurrences in a transition of positive probability qualify), composition (all sub-occurrences are evaluated), information ($\rho > 0$), integration ($\alpha > 0$: a joint occurrence must constrain its target beyond what its parts do independently), and exclusion (one maximal, minimal cause and effect). For a majority gate on four inputs with transition $ABCD = 1110 \to M = 1$, each on input and every combination of them has an actual effect on $\{M = 1\}$, but the only actual cause of $\{M = 1\}$ is $\{ABC = 111\}$; $\{D = 0\}$ contributes nothing. More generally (the source's Theorem 1, proved in its Appendix B, a result about this definition rather than part of it): if $V_t = \{Y_t\}$ is a binary unit whose $n$ equivalent inputs form $V_{t-1}$, and $Y_t$ turns on iff at least $k$ inputs are on, with $1 \le k \le n$ and at least $k$ inputs on, then the actual cause of $\{Y_t = 1\}$ is a set of exactly $k$ inputs in state $1$ (a minimally sufficient set), undetermined among such sets by symmetry when more than $k$ inputs are on; inputs in state $0$ lower the probability of $\{Y_t = 1\}$ and are part of no actual cause or effect. For $k = 0$ the unit is always on and $\{Y_t = 1\}$ has no actual cause.

## Depends on

- [Cause and effect repertoires under causal marginalization](cause-and-effect-repertoires-under-causal-marginalization.md)

## Sources

- L. Albantakis, W. Marshall, E. Hoel, G. Tononi, *What Caused What? A Quantitative Account of Actual Causation Using Dynamical Causal Networks*, Entropy 21 (2019), 459, Sections 2.3–2.4 (Eqs. 7–10, 13–16), Section 3.2 (Eq. 17) and Appendix B (Theorem 1). <https://doi.org/10.3390/e21050459> (PMCID: PMC7514949)
