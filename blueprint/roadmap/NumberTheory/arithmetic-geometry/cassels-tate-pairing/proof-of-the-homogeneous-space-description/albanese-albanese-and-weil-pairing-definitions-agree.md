# The Albanese–Albanese and Weil pairing definitions agree

Let $K$, $A$, $A^\vee$ and $\mathcal{P}$ be as in
[The Albanese–Albanese definition of the Cassels–Tate pairing](albanese-albanese-definition-of-the-cassels-tate-pairing.md), and
let $\langle\,,\rangle$ be the [Cassels–Tate pairing](../construction-of-the-cassels-tate-pairing/cassels-tate-pairing-of-an-abelian-variety.md) in its Weil pairing
definition, with $e_m$ computed through the same $\mathcal{P}$. Then for all $a \in \text{Ш}(K, A)$ and $a' \in \text{Ш}(K, A^\vee)$,

$$\langle a, a'\rangle_{\mathcal{P}} = \langle a, a'\rangle.$$

Proof (Poonen and Stoll). Let $m$ kill $a$ and $a'$ and take $\tau$, $\tau'$ and $\sigma$ as in the Weil pairing definition.
Choose $s \in C^1(G_K, Z^0(A_{\bar K}))$ representing $\sigma$, and below $\mathfrak{a}'$ and $q_v$, so that every value used
is defined (Poonen and Stoll, §12, p. 1142); then take $\alpha$ to be the image of $\tau$ in $Z^1(G_K, A(\bar K))$,
$\mathfrak{a} = ms$, $\mathfrak{a}' \in C^1(G_K, Z^0(A^\vee_{\bar K}))$ representing $\tau'$, and $\epsilon$ with $d\epsilon = \eta$. Then

$$d\sigma \vee \tau' - d\epsilon = -ds \cup (m\mathfrak{a}') + s \cup d(m\mathfrak{a}') = -d\bigl(s \cup (m\mathfrak{a}')\bigr),$$

so one may take $\bar\varepsilon = \epsilon - s \cup (m\mathfrak{a}')$. Locally, with $\beta_v$ and $Q_v$ as in both definitions, choose
$q_v \in Z^0(A_{\bar K_v})$ summing to $Q_v$ and take $b_v = mq_v$. Then

$$\bar\gamma_v = (\mathfrak{a}_v - db_v) \cup \mathfrak{a}'_v + (dq_v) \cup (m\mathfrak{a}'_v) - \epsilon_v, \qquad \gamma_v = (\mathfrak{a}_v - db_v) \cup \mathfrak{a}'_v - (mq_v) \cup d\mathfrak{a}'_v - \epsilon_v,$$

and $\bar\gamma_v - \gamma_v = d(q_v \cup (m\mathfrak{a}'_v))$ is a coboundary.

## Depends on

- [The Albanese–Albanese definition of the Cassels–Tate pairing](albanese-albanese-definition-of-the-cassels-tate-pairing.md)
- [The Cassels–Tate pairing of an abelian variety](../construction-of-the-cassels-tate-pairing/cassels-tate-pairing-of-an-abelian-variety.md)

## Proof depends on

- [The Weil pairing through a Poincaré divisor](../construction-of-the-cassels-tate-pairing/weil-pairing-through-a-poincare-divisor.md), for $e_m(x, x') = (m\mathfrak{b}) \cup \mathfrak{b}' - \mathfrak{b} \cup (m\mathfrak{b}')$
- [The Cassels–Tate pairing does not depend on the choices](../construction-of-the-cassels-tate-pairing/independence-of-the-choices-in-the-cassels-tate-pairing.md)
- [The Albanese–Albanese definition of the Cassels–Tate pairing](albanese-albanese-definition-of-the-cassels-tate-pairing.md), for the independence of its choices

## Sources

- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §12.3, Proposition 34 and its proof, p. 1147 (stated for $a$ and $a'$ of order prime to the
  characteristic of $k$, a condition that is empty over a number field).
