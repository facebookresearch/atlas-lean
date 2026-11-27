# Pathwise existence of the SIR chain

Let $\beta, \gamma \ge 0$, let $x_0 = (S_0, I_0)$ be an [SIR state](sirstate.md) with
$S_0 + I_0 \le N$, and let $e_1, e_2$ be sequences of positive interarrival times of the infection
and recovery clocks. They are arbitrary sequences, so no independence between the two clocks is
involved. Let $Y_1, Y_2$ be their [counting paths](clock-count.md). Then the counts $S, I, R$ of the
[SIR path](sir-path.md) driven by $e_1, e_2$ from $x_0$ form a
[sample path of the stochastic SIR chain](is-chain-path.md) driven by $Y_1, Y_2$: the paths
$S, I, R : \mathbb{R} \to \mathbb{N}$ are measurable, $S(0) + I(0) + R(0) = N$, and for every
$t \ge 0$, in the real numbers,

$$S(t) = S(0) - Y_1(\Lambda_1(t)),$$

$$I(t) = I(0) + Y_1(\Lambda_1(t)) - Y_2(\Lambda_2(t)),$$

$$R(t) = R(0) + Y_2(\Lambda_2(t)),$$

where $\Lambda_1(t) = \max(0, \int_0^t \beta S I / N)$ is the [infection clock](infection-clock.md)
and $\Lambda_2(t) = \max(0, \int_0^t \gamma I)$ the [recovery clock](recovery-clock.md), with
$\beta S I / N = 0$ when $N = 0$ by the convention $x / 0 = 0$. The
equations are relative to the values at time $0$; that these are $S(0) = S_0$ and $I(0) = I_0$ is
the separate result that [the SIR path starts at its initial state](sir-path-zero.md).
