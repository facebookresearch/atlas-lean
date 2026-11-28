# Hierarchical achievement scalarisation of several objectives

Objectives ranked by importance, each with a tolerance, can be merged into one scalar objective that responds, at each point, to the most important objective whose tolerance is still missed. Shifting the lower objectives keeps the merged function comparable across those regions.

Let $f_0, \dots, f_{n-1}$, $n \ge 1$, be objectives to be minimized, ordered by decreasing importance, and let $\mathcal{Y}$ be a finite nonempty set of observed parameter points. Relative tolerances $\tilde{f}^{\mathrm{tol}}_k \in [0,1]$, fixed in advance, give absolute tolerances and shifts on the nested sets $\mathcal{Y}_{-1} = \mathcal{Y}$, $\mathcal{Y}_{k} = \{\boldsymbol{x}_i \in \mathcal{Y}_{k-1} : f_k(\boldsymbol{x}_i) \le f^{\mathrm{tol}}_k\}$ by

$$
f^{\mathrm{tol}}_k = \tilde{f}^{\mathrm{tol}}_k \Big[ \max_{\boldsymbol{x}_i \in \mathcal{Y}_{k-1}} f_k(\boldsymbol{x}_i) - \min_{\boldsymbol{x}_i \in \mathcal{Y}_{k-1}} f_k(\boldsymbol{x}_i) \Big] ,
\qquad
f^{\min}_k = \min_{\boldsymbol{x}_i \in \mathcal{Y}_{k-1}} f_k(\boldsymbol{x}_i) ,
$$

which require each $\mathcal{Y}_{k-1}$ to be nonempty. Define the *success* weight and its complement by

$$
w_k(\boldsymbol{x}) = \mathbb{1}\big(f_k(\boldsymbol{x}) \le f^{\mathrm{tol}}_k\big) , \qquad \bar{w}_k = 1 - w_k ,
$$

so that $\bar{w}_k$ marks a missed tolerance. The scalarised objective is

$$
\chi(\boldsymbol{x}) = \bar{w}_0(\boldsymbol{x}) f_0(\boldsymbol{x}) + \sum_{k=1}^{n-1} \Big( \prod_{m=0}^{k-1} w_m(\boldsymbol{x}) \Big) \bar{w}_k(\boldsymbol{x}) \big( f_k(\boldsymbol{x}) - f^{\min}_{k-1} \big) + \Big( \prod_{m=0}^{n-1} w_m(\boldsymbol{x}) \Big) \big( f_0(\boldsymbol{x}) - f^{\min}_{n-1} \big) ,
$$

which equals $f_0$ where the main objective misses its tolerance, the shifted $f_k$ where objectives $0, \dots, k-1$ meet theirs and $f_k$ does not, and the shifted main objective where all are met.

Source conventions, stated because the published formulas and figure do not agree. The printed Eq. 2 is a strict step: it takes the value $0$ when the objective equals its tolerance, so equality counts as a miss there, while Fig. 1C tests $f_k \le f^{\mathrm{tol}}_k$ and so takes the satisfied branch at equality; the display above follows the figure. Eq. 3 names the Eq. 2 expression $\Theta^{+}$ and Eq. 5 multiplies $f_0$ by that $\Theta^{+}_0$ and places the all-met shifted value inside its product, whereas Fig. 1C–D return $f_0$ in the branch where the main objective misses its tolerance and place the all-met value once, outside the product of success indicators; Eq. 4's two signed steps are not exact complements at equality either. The display is therefore an explicitly chosen generalization of Fig. 1C–D, not a transcription of Eq. 5. Eq. 1 prints the tolerance as a relative factor times the observed range with no added minimum, so with observations $\{5, 7\}$ and relative tolerance $1$ the tolerance is $2$ and admits neither point; no endpoint claim about admitting the whole range is made, and no Pareto guarantee follows from the construction. Tolerances and shifts are recomputed from the observations at each iteration, so $\chi$ depends on the data as well as on $\boldsymbol{x}$.

A smooth variant, declared here as a construction rather than attributed to the source, replaces $w_k$ by the bounded logistic weight

$$
\theta_k(\boldsymbol{x}) = \Big[ 1 + \exp\Big( -\frac{f^{\mathrm{tol}}_k - f_k(\boldsymbol{x})}{\tau} \Big) \Big]^{-1} , \qquad \tau > 0 ,
$$

and $\bar{w}_k$ by $1 - \theta_k$. This is the smooth counterpart of the *success* weight, which is the direction the argument $f^{\mathrm{tol}}_k - f_k$ of Eq. 6 has. For continuous objectives the resulting function is continuous; away from ties $\theta_k \to w_k$ and $1 - \theta_k \to \bar{w}_k$ pointwise as $\tau \to 0^{+}$, while at a tie both weights equal $1/2$ for every $\tau$, so the smoothed objective does not reproduce the hard branching there and is not claimed to inherit its hierarchy.

## Depends on

None.

## Proof depends on

None.

## Expansion

A formal development takes finitely many objectives, a finite nonempty observation set with the nonemptiness of every $\mathcal{Y}_{k-1}$ as a hypothesis, and relative tolerances in $[0,1]$; it defines the nested sets, tolerances and shifts by the display, then $\chi$ both as the branching function of Fig. 1C's pseudo-code and as the weighted sum above, and proves the two agree. The smooth variant is a separate definition, with continuity for continuous objectives and the pointwise limits away from ties.

## Context

Graduate. The multi-objective scalarisation of Häse, Roch and Aspuru-Guzik for self-driving laboratories, where a chemist states a priority order and tolerances rather than weights; it feeds a single-objective planner such as the kernel-density acquisition of this chapter.

## Sources

- Florian Häse, Loïc M. Roch and Alán Aspuru-Guzik, *Chimera: enabling hierarchy based multi-objective optimization for self-driving laboratories*, Chemical Science 9 (2018) 7642–7655, Eqs. 1–6 and Figure 1C–D. DOI [10.1039/c8sc02239a](https://doi.org/10.1039/c8sc02239a), PMC6182568.
