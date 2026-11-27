# The Cassels–Tate pairing is biadditive

Let $K$, $A$ and $A^\vee$ be as in the construction of
[the Cassels–Tate pairing](../cassels-tate-pairing-of-an-abelian-variety.md). Then for $a_1, a_2, a \in \text{Ш}(K, A)$ and
$a'_1, a'_2, a' \in \text{Ш}(K, A^\vee)$,

$$\langle a_1 + a_2, a'\rangle = \langle a_1, a'\rangle + \langle a_2, a'\rangle, \qquad \langle a, a'_1 + a'_2\rangle = \langle a, a'_1\rangle + \langle a, a'_2\rangle.$$

Proof. Take $m$ killing all the elements, which is allowed as the value does not depend on $m$. For the first
identity, fix $\tau'$, and take choices $\tau_i$, $\sigma_i$, $\bar\varepsilon_i$, $\beta_{i,v}$, $Q_{i,v}$ for $a_i$. Their sums are
choices for $a_1 + a_2$: $d(\sigma_1 + \sigma_2) \vee \tau' = d(\bar\varepsilon_1 + \bar\varepsilon_2)$, as $\vee$ is biadditive, and
the cocycle $\bar\gamma_v$ for $a_1 + a_2$ is the sum of those for $a_1$ and $a_2$. The second identity follows in the same
way from choices $\tau'_i$, $\bar\varepsilon_i$ for $a'_i$ with $\tau$, $\sigma$, $\beta_v$ and $Q_v$ fixed. The value does not
depend on the choices, which gives both identities.

## Depends on

- [The Cassels–Tate pairing of an abelian variety](../cassels-tate-pairing-of-an-abelian-variety.md)

## Proof depends on

- [The Cassels–Tate pairing does not depend on m](independence-of-m-in-the-cassels-tate-pairing.md), for a common $m$
- [The Cassels–Tate pairing does not depend on the choices](independence-of-the-choices-in-the-cassels-tate-pairing.md)
- [The Weil pairing is biadditive, Galois-equivariant and compatible in m](bilinearity-of-the-weil-pairing.md), for the biadditivity of $\vee$ (its item 1)

## Sources

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Proposition 6.9, p. 78 (the canonical pairings), and the proof of Lemma 6.17, p. 87, which uses
  $\langle ma_0, a'\rangle = \langle a_0, ma'\rangle$.
- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §2, p. 1112 (bilinear pairings), and §12.2, pp. 1143–1144 (the Weil pairing definition).
