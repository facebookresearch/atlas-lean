# Counting integers with a given least prime factor in an interval

Let $a$ and $t$ be
positive integers and let $p$ be a prime. Let $N$ be the number of integers $m$ with
$a + 1 \le m \le a + t$ that are divisible by $p$ and by no prime $q < p$. Then

$$\left| N - \frac{t}{p} \prod_{q < p,\ q \text{ prime}} \left(1 - \frac{1}{q}\right) \right|
\le 2^{\pi(p-1)}$$

where $\pi$ is the prime-counting function.

## Sources

- Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of Integer Sequences 29 (2026), Article 26.1.4, Lemma 6 (`lem:Dp`).
