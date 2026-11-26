# Power branch, $K>0$, $0<a_0<a_c$, base $>0$: $a<a_c$ iff $N<N_f$

Let $K > 0$, $r \ne 0$ and $0 < a_0 < a_c$, and let $N$ be a cycle count at which the base
$B(N) = a_0^r + r K N$ is positive. Then the [power-branch crack](paris-crack-pow.md)
$a(N) = \bigl(a_0^r + r K N\bigr)^{1/r}$ is below the target length exactly before the
[Paris life](paris-life-pow.md) $N_f = (a_c^r - a_0^r)/(rK)$:

$$a(N) < a_c \iff N < N_f,$$

both inequalities strict. The positive base is needed: for $r < 0$, at the blow-up cycle count
$N^* = a_0^r/(-rK)$, where the base vanishes, the formula gives $a(N^*) = 0 < a_c$ by the convention
$0^t = 0$ for $t \ne 0$, although $N^* > N_f$ ([life before blow-up](paris-life-pow-lt-blowup.md)).
