# Locally identifiable specializations of rational ODE models

**Setting.** Consider a rational ODE model with parameters $\bar\alpha$, states $\bar x$, inputs $\bar u$ and outputs $\bar y$,

$$\Sigma(\bar\alpha):\qquad \bar x'=\bar f(\bar x,\bar\alpha,\bar u),\qquad \bar y=\bar g(\bar x,\bar\alpha,\bar u),$$

with $\bar f,\bar g$ rational. Its **input-output (IO) equations** generate the elimination ideal of the model's differential ideal in the differential polynomial ring in $\bar y,\bar u$. The **field of IO-identifiable functions** is the smallest field $k$ with $\mathbb Q\subseteq k\subseteq\mathbb Q(\bar\alpha)$ over which these IO relations are defined; $h\in\mathbb Q(\bar\alpha)$ is IO-identifiable if $h\in k$ and locally IO-identifiable if $h$ is algebraic over $k$. Non-identifiability (for example only $a,c,d$ identifiable in the Lotka-Volterra model $x_1'=ax_1-bx_1x_2$, $x_2'=-cx_2+dx_1x_2$, $y=x_1$, whose IO equation is $yy''-y'^2-dy^2y'+cyy'+ady^3-acy^2=0$) prevents meaningful parameter estimation.

**Theorem.** For every such model there is a tuple $\widetilde\alpha$, of the same length as $\bar\alpha$, with entries algebraic over $\mathbb Q(\bar\alpha)$, such that
1. every entry of $\widetilde\alpha$ is locally IO-identifiable, and
2. $\Sigma(\widetilde\alpha)$ (the same equations with $\bar\alpha$ replaced by $\widetilde\alpha$) has the same IO equations as $\Sigma(\bar\alpha)$.

So $\Sigma(\widetilde\alpha)$ is a locally identifiable reparametrization of the same shape: the same monomials in the new state variables. If moreover the IO equations $E_1,\dots,E_m$ satisfy $\sum_i\operatorname{ord}_{\bar y}E_i=n=\dim\bar x$ (equivalently, all states are locally observable when the parameters are known), then the new states are algebraic functions of $\bar x$ and $\bar\alpha$, giving an explicit state transformation.

## Expansion

The proof is constructive. Write generators of the field of IO-identifiable functions as $\beta_j=p_j(\bar\alpha)$. Express $y,y',\dots,y^{(m)}$ as rational functions of $\bar x$ via Lie derivatives, take their Jacobian $M$ with respect to $\bar x$, a non-singular maximal minor $D$, and a non-zero coefficient $D_0(\bar\alpha)$ of its numerator. Then solve, over $\mathbb Q(\bar\beta)$, the system $\beta_j=p_j(\widetilde\alpha)$ for all $j$ together with the inequation $D_0(\widetilde\alpha)\,C(\widetilde\alpha)\ne0$ ($C$ a common denominator of the model's coefficients). Any algebraic solution gives the specialization, and equating old and new Lie derivatives gives the change of states. For Lotka-Volterra the system is $\widetilde\alpha_1=a$, $\widetilde\alpha_3=c$, $\widetilde\alpha_4=d$, $\widetilde\alpha_2\ne0$; choosing $\widetilde\alpha_2=1$ gives $w_1'=aw_1-w_1w_2$, $w_2'=-cw_2+dw_1w_2$ with $w_1=x_1$, $w_2=bx_2$. Unlike scaling-based methods the construction can produce non-scaling reparametrizations, illustrated on a chemical reaction network, a bilinear model with input, the Goodwin oscillator, a blood coagulation model and an Akt pathway model. For some models global identifiability cannot be achieved by any reparametrization.

## Sources

- A. Ovchinnikov, A. Pillay, G. Pogudin, T. Scanlon, "Identifiable specializations for ODE models", *Systems & Control Letters* 204 (2025), 106226, Section 2 (Definition 1, Theorem 1, Section 2.3), Section 3 (constructive proof) and Section 4 (examples, including Section 4.4 Lotka-Volterra), <https://doi.org/10.1016/j.sysconle.2025.106226> (preprint arXiv:2308.16273).
