# Global nonnegative trajectories exist from nonnegative data

Let $k_1, k_b, k_2 \ge 0$ and $s_0, c_0, e_0, p_0 \ge 0$. Then there is a
[solution](../is-solution.md) $(s, c, e, p)$ of the Michaelis–Menten mass-action system with
$(s(0), c(0), e(0), p(0)) = (s_0, c_0, e_0, p_0)$ such that, for every $t \ge 0$,

- $s(t), c(t), e(t) \ge 0$ and $p(t) \ge p_0$;
- the total enzyme $e(t) + c(t) = e_0 + c_0$ and the total substrate
  $s(t) + c(t) + p(t) = s_0 + c_0 + p_0$ are conserved;
- each of $s$, $c$ and $e$ that starts positive stays positive.

The derivatives are two-sided at every $t \ge 0$. The initial complex $c_0 \ge 0$ is arbitrary: it
need not be the [quasi-steady-state value](../qss-complex.md).
