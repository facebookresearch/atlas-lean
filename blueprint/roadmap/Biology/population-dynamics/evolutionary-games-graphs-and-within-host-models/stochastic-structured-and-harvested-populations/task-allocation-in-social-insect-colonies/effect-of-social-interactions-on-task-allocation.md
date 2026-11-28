# Effect of social interactions on task allocation

**Setting.** In the two-task social insect colony model (inside task 1 with mortality $\mu_1$, outside task 2 with mortality $\mu_2>\mu_1$, relative demands $\hat D_i=\gamma_i/(\theta_i\alpha_i)$, Allee exponent $s=2$, condition **H** of the response threshold model), the equilibrium inside allocation $x_1^R$ of the full model solves

$$
(1-x_1)^2=\frac{\mu_1\hat D_2}{\mu_2\hat D_1}x_1^2+SI(x_1),\qquad SI(x_1)=\frac{x_1(1-x_1)}{\mu_2}\Bigl[\Bigl(1+\frac{\hat D_2}{\hat D_1}\Bigr)x_1-1\Bigr],
$$

where $SI$ is the contribution of social-contact-driven task switching.

**Lemma (no social interactions).** If the social switching term is removed from the model, the task allocation is unique and explicit:

$$
x_1^{NS}=\frac{1}{1+\sqrt{\dfrac{\mu_1\hat D_2}{\mu_2\hat D_1}}},\qquad x_2^{NS}=1-x_1^{NS};
$$

thus $x_1^{NS}<x_2^{NS}$ if $\mu_1/\mu_2>\hat D_1/\hat D_2$ and $x_1^{NS}>x_2^{NS}$ if $\mu_1/\mu_2<\hat D_1/\hat D_2$.

**Theorem (direction of the social effect).** Let $x_1^{SI}=1/(1+\hat D_2/\hat D_1)$, the zero of $SI$ in $(0,1)$ ($SI>0$ above it, $SI<0$ below). Then

1. if $\mu_1/\mu_2>\hat D_2/\hat D_1$, then $x_1^{NS}<x_1^R<x_1^{SI}$;
2. if $\mu_1/\mu_2<\hat D_2/\hat D_1$, then $x_1^{SI}<x_1^R<x_1^{NS}$.

## Depends on

- [Colony size and task allocation equilibria in a response threshold model](colony-size-and-task-allocation-equilibria-in-a-response-threshold-model.md)

## Expansion

Without social switching, the allocation balances recruitment proportional to the relative stimulus against task-specific mortality, which gives $(1-x_1)^2=\frac{\mu_1\hat D_2}{\mu_2\hat D_1}x_1^2$ and the square-root formula: the inside share is governed by the ratio of the relative cost $\mu_1/\mu_2$ to the relative demand $\hat D_1/\hat D_2$. The social term pulls the allocation toward the demand-proportional value $x_1^{SI}$, at which it vanishes; comparing the curves $(1-x_1)^2$ and $\frac{\mu_1\hat D_2}{\mu_2\hat D_1}x_1^2+SI(x_1)$ on either side of $x_1^{SI}$ places the full equilibrium between $x_1^{NS}$ and $x_1^{SI}$. Biologically, contacts send foragers back inside when the product of mortality and demand of the inside task dominates, and recruit more foragers otherwise.

## Sources

- Yun Kang, Guy Theraulaz, *Dynamical models of task organization in social insect colonies*, arXiv (2015). Section 3: Lemma 3.3 (task allocation without social interactions), Theorem 3.3 (contribution of social interactions). <https://doi.org/10.48550/arXiv.1511.04769> Published version: Bulletin of Mathematical Biology 78 (2016) 879–915, <https://doi.org/10.1007/s11538-016-0165-1>.
