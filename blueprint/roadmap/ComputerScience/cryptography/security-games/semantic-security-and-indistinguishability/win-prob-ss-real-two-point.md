# Semantic security implies indistinguishability, per adversary

Let $D$ be a distinguisher and $m \ne m'$ two messages of the same length. Take the
[two-point distribution](../games-and-advantages/two-point.md) on $m$ and $m'$ as plaintext
distribution, no a priori information, and the target function $f(x) = [x = m']$. Let $A$ be the
adversary that outputs $D(pk, c, r)$. Then for every ideal adversary $A'$,

$$\Pr[A \text{ wins}] - \Pr[A' \text{ wins}] = \tfrac12 \bigl(\Pr[D(\mathrm{Enc}(m')) = 1] - \Pr[D(\mathrm{Enc}(m)) = 1]\bigr),$$

the probabilities being those of the [real](ss-real.md) and [ideal](ss-ideal.md) experiments and of
the [indistinguishability experiments](ind-exp.md) for $m'$ and $m$. Indeed $A'$ sees the same
length and the same (empty) information for both messages, so it wins with probability exactly
$\tfrac12$. So a distinguisher with advantage $\delta$ gives, with one call, an adversary that beats
every simulator by $\delta / 2$.

## Informally uses

- [Averaging over the two-point distribution](../games-and-advantages/win-prob-two-point-bind.md)

## Sources

- O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University Press, 2004, Section 5.2, Proposition 5.2.7 and its proof (Section 5.2.3.2), conditions 1 to 3 (two-point plaintext
  distribution, information depending only on the length, Boolean target).
