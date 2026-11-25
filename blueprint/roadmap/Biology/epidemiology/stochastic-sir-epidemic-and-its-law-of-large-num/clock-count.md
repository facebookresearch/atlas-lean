# Counting path of a unit clock

For a real sequence $e$ of interarrival times and a time $u \ge 0$, the counting path at $u$ is

$$Y(u) = \#\{n \in \mathbb{N} : e(0) + e(1) + \dots + e(n) \le u\},$$

taken to be $0$ when this set is infinite, for example when every $e(n)$ is $0$, or when the
$e(n)$ are positive with sum at most $u$. When the $e(n)$ are positive, the $(n+1)$-th arrival is
at time $e(0) + \dots + e(n)$, and $Y(u)$ is the number of arrivals in $[0, u]$ whenever that
number is finite. In the notation of
[counting processes](../../../Probability/point-processes/poisson-processes/count.md), $Y(u)$ is the
count at time $u$ of the interarrival times $e(0), e(1), \dots$.
