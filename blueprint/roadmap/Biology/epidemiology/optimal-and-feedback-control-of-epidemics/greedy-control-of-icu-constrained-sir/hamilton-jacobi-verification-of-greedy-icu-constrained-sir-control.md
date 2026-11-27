# Hamilton–Jacobi verification of greedy control for the ICU-constrained SIR model

**Model.** Susceptible and infected proportions evolve under a contact-reduction control $a(t) \in [0, \bar a]$, $\bar a \in (0,1)$:

$$
\dot s = -\beta(1-a)\,s\,i, \qquad \dot i = \big(\beta(1-a)s - \gamma\big)\,i,
$$

with $0 < \gamma < \beta(1-\bar a)$ and $(s_0, i_0)$ in the triangle $\{s, i \ge 0,\ s + i \le 1\}$. An ICU capacity imposes the state constraint $i(t) \le i^*$. The **green zone** $\mathcal{G} = \{s_0 \le \phi(i_0)\}$ is the set of states that respect the constraint with no intervention, and the **yellow zone** $\mathcal{Y} = \{s_0 \le \psi(i_0)\}$ the set that can be kept below $i^*$ by some admissible control; here $x = \phi(i) \ge \gamma/\beta$ solves $-x + \frac{\gamma}{\beta}\log x = i - i^* + \frac{\gamma}{\beta}\log\frac{\gamma}{\beta} - \frac{\gamma}{\beta}$, and $\psi$ is defined the same way with $\gamma/\beta$ replaced by $\gamma/(\beta(1-\bar a))$.

**Control problem.** For $(s_0, i_0) \in \mathcal{Y}$ minimize, over controls keeping $i \le i^*$,

$$
J(s_0, i_0, a) = \int_0^{\infty} l_1\big(s(t), i(t), a(t)\big)\,\mathbf{1}_{s(t) \ge \phi(i(t))}\,dt,
$$

where the running cost $l_1 \ge 0$ is lower semicontinuous, nondecreasing in $a$, has convex value sets $\{l_1(s,i,a) : a \in [0,\bar a]\}$, and satisfies $l_1(s, i, 0) = 0$ on $\mathcal{G}$. The **greedy feedback** acts only on the active boundary $\partial\mathcal{Y}^+ = \big([\frac{\gamma}{\beta}, \frac{\gamma}{\beta(1-\bar a)}] \times \{i^*\}\big) \cup \{(\psi(i), i) : 0 < i \le i^*\}$:

$$
a^*(s, i) = \Big[\Big(1 - \frac{\gamma}{\beta s}\Big)^{+} \wedge \bar a\Big]\,\mathbf{1}_{\partial\mathcal{Y}^+}(s, i).
$$

It does nothing until the state is about to leave $\mathcal{Y}$, then applies $\bar a$ along $s = \psi(i)$ and, once $i = i^*$, the minimal control $1 - \gamma/(\beta s)$ that holds $i$ at capacity.

**Theorem.** The cost $W = J(\cdot, \cdot, a^*)$ of the greedy policy is explicit: $W = 0$ on $\mathcal{G}$; for states whose uncontrolled trajectory first hits the capacity line at $(s_1, i^*)$,

$$
W(s_0, i_0) = \frac{1}{\gamma i^*}\int_{\gamma/\beta}^{s_1} l_1\Big(u, i^*, 1 - \frac{\gamma}{\beta u}\Big)\,du, \qquad s_1 - s_0 - i_0 + i^* - \frac{\gamma}{\beta}\log\frac{s_1}{s_0} = 0,
$$

and for states that first reach $s = \psi(i)$, the cost of riding that boundary with $\bar a$ is added. If $l_1$ is continuous, $W$ is continuous and differentiable almost everywhere on $\mathcal{Y}$. Put $\tilde l_1(s, i, a) = l_1(s,i,a)/(\gamma i a)$. If the cost per unit of control at the point where the greedy policy acts (on the capacity line, or on the boundary $s = \psi(i)$) is at most $\min_{a \in (0, \bar a]} \tilde l_1(s_0, i_0, a)$, then $W$ satisfies the Hamilton–Jacobi equation

$$
\sup_{a \in [0, \bar a]}\Big\{\partial_s W\,\beta(1-a)s i - \partial_i W\,\big(\beta(1-a)s - \gamma\big)i - l_1(s,i,a)\,\mathbf{1}_{s \ge \phi(i)}\Big\} = 0
$$

wherever it is differentiable. This condition holds for state-dependent costs $l_1 = \lambda(s,i)\,a$ with $\lambda \ge 0$ uniformly continuous, nondecreasing in $s$, and with $\lambda(s,i)/i$ nonincreasing in $i$ (for example $\lambda i^{\eta} a$ with $0 \le \eta \le 1$).

## Expansion

Along the uncontrolled flow $s + i - \frac{\gamma}{\beta}\log s$ is conserved, which locates the entry point $s_1$ on the capacity line; there the greedy control keeps $i \equiv i^*$, so $s$ decreases linearly at rate $\gamma i^*$ until $s = \gamma/\beta$, where the epidemic turns over and the state is green. Changing variables from time to $s$ gives the integral. Implicit differentiation of the equation for $s_1$ gives $\partial_s W = \tilde l_1(s_1, i^*, \cdot)\,(\beta s_0 - \gamma)/(\beta s_0)$ and $\partial_i W = \tilde l_1(s_1, i^*, \cdot)$. Inserting these into the Hamiltonian makes it equal to $\gamma i_0 a\,[\tilde l_1(s_1, i^*, \cdot) - \tilde l_1(s_0, i_0, a)]$, which is nonpositive under the stated condition and vanishes at $a = 0$. Combined with a comparison principle for state-constrained Hamilton–Jacobi equations, this verification shows that the greedy policy is optimal, and the condition is also necessary for that. The approach avoids the Pontryagin analysis and handles state-dependent costs.

## Sources

- Lorenzo Freddi, Dan Goreac, Juan Li, Boxiang Xu, "SIR Epidemics with State-Dependent Costs and ICU Constraints: A Hamilton–Jacobi Verification Argument and Dual LP Algorithms", Applied Mathematics & Optimization 86 (2022), 23, <https://doi.org/10.1007/s00245-022-09884-x>. Published version of arXiv:2110.11625, cited next; locators there refer to the arXiv version.
- Lorenzo Freddi, Dan Goreac, Juan Li, Boxiang Xu, *SIR Epidemics With State-Dependent Costs and ICU Constraints: A Hamilton-Jacobi Verification Argument and Dual LP Algorithms*, arXiv 2021. Theorem 1 (green and yellow zones, quoted from earlier work), Section 3: Lemma 1 (explicit cost of the greedy policy), Theorem 2 (regularity of $W$ and Hamilton–Jacobi equation), Example 2. <https://doi.org/10.48550/arXiv.2110.11625>
