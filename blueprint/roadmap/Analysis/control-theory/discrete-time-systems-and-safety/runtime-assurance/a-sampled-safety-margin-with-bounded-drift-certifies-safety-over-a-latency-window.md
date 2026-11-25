# A sampled safety margin with bounded drift certifies safety over a latency window

Let $x(t)$ be a trajectory, $m$ a real-valued **safety margin** (safe means $m(x(t)) > 0$), and suppose a monitor samples an observation at time $t_s$ and computes an estimate $\hat m$ of the margin with

$$|m(x(t)) - \hat m| \le \varepsilon + \bar v\,(t - t_s) \qquad \text{for all } t \ge t_s,$$

where $\varepsilon \ge 0$ bounds the observation error and $\bar v \ge 0$ bounds the rate at which the margin can change. If $\hat m > \varepsilon + \bar v\,\tau_{\max}$ for a latency bound $\tau_{\max} \ge 0$, then $m(x(t)) > 0$ for every $t \in [t_s, t_s + \tau_{\max}]$.

So a decision taken at the sample time remains valid until a switch decided then has taken effect, provided the observed margin exceeds the error plus the worst drift over the latency. The threshold cannot be lowered in general: if $\hat m = \varepsilon + \bar v\,\tau_{\max}$, the trajectory with $m(x(t)) = \hat m - \varepsilon - \bar v\,(t - t_s)$ satisfies the hypothesis and reaches $m = 0$ at $t = t_s + \tau_{\max}$.

**Proof.** For $t \in [t_s, t_s + \tau_{\max}]$, $m(x(t)) \ge \hat m - \varepsilon - \bar v\,(t - t_s) \ge \hat m - \varepsilon - \bar v\,\tau_{\max} > 0$. The extremal trajectory meets the hypothesis with equality.

## Sources

- K. L. Hobbs, M. L. Mote, M. C. L. Abate, S. D. Coogan and E. M. Feron, "Runtime assurance for safety-critical systems: an introduction to safety filtering approaches for complex control systems", *IEEE Control Systems Magazine* 43(2), 2023, <https://arxiv.org/abs/2110.03506>, "The Simplex Architecture" (a boundary monitor watching for imminent violations of safety constraints and decision logic switching to a backup controller, pp. 27–28) and the discussion of latched and unlatched switching (pp. 20–21). The margin bound for sampled monitoring with latency is derived on the page.
