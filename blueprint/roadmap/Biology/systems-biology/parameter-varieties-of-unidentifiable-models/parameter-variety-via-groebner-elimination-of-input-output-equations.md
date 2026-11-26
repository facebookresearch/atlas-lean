# Parameter variety of an unidentifiable state-space model via Gröbner elimination

**Setting.** Consider a polynomial state-space model on $[T_0,T_1]$,
$$
\frac{dx}{dt} = f(x,u;a),\qquad y = g(x,u;a),
$$
with state $x(t)\in\mathbb{R}^N$, input $u(t)\in\mathbb{R}^M$, scalar output $y(t)$, unknown parameters $a\in\mathbb{R}^n$, and $f,g$ polynomial in $(x,u)$. The model is (structurally) unidentifiable if for every input there are $a_\alpha\ne a_\beta$ giving the same output. Suppose the inputs, the output and their time derivatives are observed at finitely many times $t_1,\dots,t_L$.

**Parameter variety.** The parameter variety of the model given the data is the set of parameters $a$ for which the model reproduces the observed inputs and output (with their derivatives) at the measurement times. It is the set of parameters that the data determine uniquely as a set, even when no single parameter is determined.

**Construction.** Differentiate the model equations enough times to form the ideal
$$
I = \Big\langle x^{(1)} - f,\ \dots,\ x^{(L)} - \tfrac{d^{L-1}}{dt^{L-1}}f,\ \ y - g,\ \dots,\ y^{(L)} - \tfrac{d^{L}}{dt^{L}}g\Big\rangle
$$
over the coefficient field $\mathbb{C}(a)$, and compute its reduced Gröbner basis for a lexicographic order with all state derivatives above all output derivatives, above all input derivatives. By the elimination theorem, the basis elements free of $x$ generate $I\cap\mathbb{C}(a)[y,\dots,y^{(L)},u,\dots,u^{(L)}]$; normalizing, this gives an input–output equation
$$
\sum_{l=1}^{L} c_l(a)\, f_l\big(u,\dots,u^{(N)},y,\dots,y^{(N)}\big) = f_{L+1}\big(u,\dots,u^{(N)},y,\dots,y^{(N)}\big),
$$
with known differential monomials $f_l$ and coefficients $c_l(a)$ rational in $a$. Substituting the data at the $L$ time points gives a linear system for the coefficient values $v_l$.

**Theorem.** The parameter variety is contained in the algebraic variety $\{a : c_l(a) = v_l,\ l = 1,\dots,L\}$, which can be written explicitly through a Gröbner basis in the parameters. When the linear system is nonsingular, the data determine the values $v_l$ of the identifiable combinations $c_l(a)$ uniquely even though $a$ is not identifiable.

**Example (hepatitis C viral dynamics under interferon).** With infected cells $x_2$, viral load $y = x_3$, infected-cell death rate $a_4$, drug efficacy $a_5\in[0,1]$, virion production rate $a_6$ and clearance rate $a_7$, the reduced model $\dot x_2 = (a_4a_7/a_6)x_3 - a_4x_2$, $\dot x_3 = (1-a_5)a_6x_2 - a_7x_3$, $x_2(T_0) = (a_7/a_6)x_3(T_0)$ has input–output equation
$$
a_4a_5a_7\, y + (a_4+a_7)\,\dot y = -\ddot y .
$$
Two measurement times determine $(v_1,v_2)$, so the data fix only the curve $\{a_4a_5a_7 = v_1,\ a_4+a_7 = v_2\}$ in $(a_4,a_5,a_7)$-space, and $a_6$ is not constrained at all. Exploring this curve reveals parameter combinations consistent with the same viral-load data that a single least-squares fit misses.

## Expansion

If $a$ lies in the parameter variety, the observed inputs and outputs extend to a common root of the differentiated model at each $t_i$, and the projection of that root set to the $(y,u)$-coordinates lies in the variety of the elimination ideal (closure theorem). So the data satisfy the input–output equation with coefficients $c_l(a)$, which yields $c_l(a) = v_l$. The number of required time points $L$ equals the number of unknown coefficients and is bounded in terms of the model. In practice the derivatives are estimated from the time series (by smoothing or Gaussian-process pseudo-data), and robustness to measurement noise is not covered by the theorem.

## Sources

- M. Komatsu, T. Yaguchi, "Method for estimating hidden structures determined by unidentifiable state-space models and time-series data based on the Groebner basis", arXiv:2012.11906 (2020), Section 2 (definitions of unidentifiability and the parameter variety), Section 3 (the method), Section 4 (application to the hepatitis C model) and Section 5.2 (main containment theorem), <https://doi.org/10.48550/arXiv.2012.11906>.
