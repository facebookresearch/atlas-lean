# Feedback can stabilise every system with uncertainty below $3/2 + \sqrt 2$

Consider $y_{t+1} = f(y_t) + u_t + w_{t+1}$ with $f : \mathbb R \to \mathbb R$ unknown and noise bounded by $W > 0$. The
uncertainty of $f$ is measured by the generalized Lipschitz quasi-norm
$\|f\| = \lim_{a \to \infty} \sup_{x, x'} |f(x) - f(x')| / (|x - x'| + a)$; $\|f\| \le L$ holds exactly when for every
$L' > L$ there is $a$ with $|f(x) - f(x')| \le L' (|x - x'| + a)$ for all $x, x'$, the form used here.

If $L < 3/2 + \sqrt 2$, there is a feedback law $u_t = h_t(y_0, \dots, y_t)$, with each $h_t$ Lebesgue measurable, such that
for every noise bound $W > 0$, every $f$ with $\|f\| \le L$, every noise sequence with $|w_t| \le W$ and every initial
value $y_0$, the closed loop satisfies $\sup_t (|y_t| + |u_t|) < \infty$. As in the source, one law serves every noise
bound, which it does not know.

Source: Xie and Guo, *How much uncertainty can be dealt with by feedback?*, IEEE Trans. Automat. Control 45(12) (2000)
2203–2217, as stated in Guo, *Exploring the capability and limits of the feedback mechanism*, Proc. ICM 2002, Vol. III (arXiv:math/0305011), Theorem 4.1(i); the original paper was not consulted. Guo's Remark 4.1 describes the
stabilising law: it estimates $f(y_t)$ by the nearest neighbour among past data and switches between a feedback that
steers the output to the centre of the range observed so far and a tracking feedback.

**Differences from the source.** None: measurability is Lebesgue measurability, as in the source (preimages of Borel
sets are Lebesgue measurable subsets of $\mathbb R^{t+1}$). Non-degenerate instance of the hypotheses: $f(x) = 2x$ has
$\|f\| = 2 < 3/2 + \sqrt 2$, so a single law stabilises it together with every other $f$ in the ball.

## Background

- [Controllable linear systems have a Hurwitz closed loop](../pole-placement/exists-is-hurwitz-add-mul.md): Coron's
  stabilisation of a known linear system by linear feedback; here $f$ is unknown and the feedback must learn it.
