# Identifiability and observability of the SIR model with quarantine

**Models.** For a population of known size $N$, with susceptibles $S$, unidentified infected $I$, quarantined infected $Q$ and recovered $R$,

$$\dot S=-\beta S\frac{I}{N-Q},\qquad \dot I=\beta S\frac{I}{N-Q}-(\rho+\alpha)I,\qquad \dot Q=\alpha I-\rho Q,\qquad \dot R=\rho I+\rho Q,$$

with transmission rate $\beta$, recovery rate $\rho$ (common to $I$ and $Q$) and quarantine rate $\alpha$; the simplified model replaces $N-Q$ by $N$. Assume $\mathcal R_0=\beta/(\rho+\alpha)>1$. The initial state is $(N-\varepsilon,\varepsilon,0,0)$ with $\varepsilon\in(0,N)$, and the observation is

$$y(t)=\big(y_1(t),y_2(t)\big)=\big(\alpha I(t),\,Q(t)\big),$$

the flow into quarantine and the quarantined population.

**Definition.** The model is identifiable if for some $t>0$ the map $(\alpha,\beta,\rho)\in(\mathbb R_{>0})^3\mapsto y|_{[0,t]}$ is injective; it is identifiable and observable if moreover $(\alpha,\beta,\rho,\varepsilon)\mapsto y|_{[0,t]}$ is injective on $(\mathbb R_{>0})^3\times(0,N)$.

**Proposition.** Both the model with quarantine-corrected mixing ($N-Q$) and the simplified model ($N$) are identifiable and observable for the observation $y$.

**Observer.** Under the additional assumption $\alpha\le\rho$, an explicit seven-dimensional observer driven by $\log y_1$, $\log y_2$ and $y_1$, with gains given by elementary symmetric polynomials of two positive vectors $\lambda\in\mathbb R^4$, $\mu\in\mathbb R^3$, produces estimates $\hat\rho$, $\hat\beta$, $\hat\alpha=\hat\beta-\hat\delta$ and $\hat I=y_1/\hat\alpha$ whose errors decay exponentially at a rate that can be made as fast as desired by taking $\min_{i,j}\min(\lambda_i,\mu_j)$ large, as long as $S(t)/N$ stays close to $1$.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

The proofs express parameters and the unmeasured states algebraically through the output and its derivatives. Since $\dot Q(0)=\alpha\varepsilon>0$, $Q(t)>0$ for $t>0$ and the quarantine equation gives $\rho=(y_1-\dot y_2)/y_2$. Next $h_1=\dot y_1/y_1$ equals $\beta S/(N-Q)-\alpha-\rho$ (or, for the simplified model, $h_1+\rho=\beta S/N-\alpha$), and differentiating again eliminates $S$, leaving a polynomial relation in $X=-\beta I+\dot Q$ whose coefficients are known output functions. In the full model it is a quadratic with a unique negative root for small $t>0$ (signs fixed at $t=0$ using $\mathcal R_0>1$), which yields $\alpha$, then $\varepsilon=y_1(0)/\alpha$ and $\beta$. At $t=0$ itself, and as $I,Q\to0$ for large times, the system is not infinitesimally identifiable, which is why the definition asks for injectivity on a positive time window and why the source estimates parameters dynamically with an observer tuned for fast error decay during the initial transient rather than for asymptotic convergence.

## Sources

- F. Hamelin, A. Iggidr, A. Rapaport, G. Sallet, M. Souza, "About the identifiability and observability of the SIR epidemic model with quarantine", IFAC-PapersOnLine 56 (2023), 4025–4030, <https://doi.org/10.1016/j.ifacol.2023.10.1384>. Published version of arXiv:2103.04614, cited next; locators there refer to the arXiv version.
- F. Hamelin, A. Iggidr, A. Rapaport and G. Sallet, "Identifiability and observability of the SIR model with quarantine", arXiv:2103.04614 (2021), Sections 2 and 3 (models, Assumption 1, Definition 1), Section 4 (Proposition 1), Section 5 (Proposition 2) and Section 6 (Assumption 2 and Proposition 3, the observer), <https://doi.org/10.48550/arXiv.2103.04614>.
