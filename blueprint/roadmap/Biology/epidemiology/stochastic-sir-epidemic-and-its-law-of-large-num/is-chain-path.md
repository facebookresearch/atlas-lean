# Random time-change equations of the stochastic SIR chain

Let $\beta$ and $\gamma$ be real numbers, $N$ a natural number, and
$y_1, y_2 \colon [0, \infty) \to \mathbb{N}$ two functions (in the intended use, paths of two
unit-rate counting processes). Paths $S, I, R \colon \mathbb{R} \to \mathbb{N}$ form a sample path
of the stochastic SIR chain of population size $N$ driven by $y_1$ and $y_2$ (Kurtz's random
time-change representation; Ethier–Kurtz 1986, ch. 6, (4.1) and ch. 11, (2.1)) if
$S(0) + I(0) + R(0) = N$, the three paths are measurable, and for every $t \ge 0$, in the real
numbers,

$$S(t) = S(0) - y_1(\Lambda_1(t)),$$

$$I(t) = I(0) + y_1(\Lambda_1(t)) - y_2(\Lambda_2(t)),$$

$$R(t) = R(0) + y_2(\Lambda_2(t)),$$

where $\Lambda_1(t) = \max(0, \int_0^t \beta S I / N)$ is the [infection clock](infection-clock.md)
and $\Lambda_2(t) = \max(0, \int_0^t \gamma I)$ the [recovery clock](recovery-clock.md). Nothing is
required of $y_1$ and $y_2$ beyond these equations. The counts are natural numbers, so they are
nonnegative by construction; measurability (which a càdlàg path has) makes the clocks Lebesgue
integrals. For $\beta, \gamma \ge 0$, $N \ge 1$, independent unit-rate
[Poisson processes](../../../Probability/point-processes/poisson-processes/is-poisson-process.md) $y_1$, $y_2$ and an initial state independent of
$(y_1, y_2)$, these are the equations of the continuous-time Markov chain that jumps
$(S, I, R) \to (S - 1, I + 1, R)$ at rate $\beta S I / N$ (infection) and
$(S, I, R) \to (S, I - 1, R + 1)$ at rate $\gamma I$ (recovery).
