# The SIR path solves the time-change equations at each time $t \ge 0$

Let $\beta, \gamma \ge 0$, let $x_0 = (S_0, I_0)$ be an [SIR state](sirstate.md) with
$S_0 + I_0 \le N$, and let $e_1, e_2$ be sequences of positive interarrival times, with
[counting paths](clock-count.md) $Y_1, Y_2$. Let $S, I, R$ be the [susceptible](sir-s.md),
[infective](sir-i.md) and [removed](sir-r.md) counts of the [SIR path](sir-path.md) driven by
$e_1, e_2$ from $x_0$, and let $\Lambda_1(t) = \max(0, \int_0^t \beta S(s) I(s) / N \, ds)$
and $\Lambda_2(t) = \max(0, \int_0^t \gamma I(s) \, ds)$ be the
[infection clock](infection-clock.md) and the [recovery clock](recovery-clock.md), where
$\beta S I / N$ is $0$ when $N = 0$ by the convention $x / 0 = 0$; for $t \ge 0$ the integrals
are nonnegative, so the maximum with $0$ has no effect. Then at every time
$t \ge 0$, in the real numbers,

$$S(t) = S_0 - Y_1(\Lambda_1(t)), \qquad I(t) = I_0 + Y_1(\Lambda_1(t)) - Y_2(\Lambda_2(t)),$$

and, in the natural numbers, $S(t) + I(t) \le N$ and

$$R(t) = (N - S_0 - I_0) + Y_2(\Lambda_2(t)).$$
