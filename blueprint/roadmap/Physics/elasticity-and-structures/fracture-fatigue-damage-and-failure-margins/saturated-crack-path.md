# Saturated crack event path under a constant load frequency

For a function $a : \mathbb{R} \to \mathbb{R}$ (crack length against the number of load cycles) and
real numbers $f$ and $N_f$, the event path is the function of time $t \ge 0$

$$d(t) = a(\min(f t, N_f)) .$$

In the model $f \ge 0$ is a constant load frequency (cycles per unit time) and $N_f \ge 0$ the
number of cycles to failure. Then $d(t) = a(f t)$, the crack after $f t$ cycles, while
$f t \le N_f$, and $d(t) = a(N_f)$ once $f t \ge N_f$, that is from the time $N_f / f$ on when
$f > 0$; at $f = 0$ the path is the constant $a(0)$. The part after $N_f$ cycles is an event model,
not continued crack growth. The definition accepts any real $f$ and $N_f$.
