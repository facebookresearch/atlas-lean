# Chinese remainder lifts into the Jacobi agreement set

Let $n$ be an odd squarefree natural
number, $p'$ a prime divisor of $n$ and $n' = n/p'$. For a residue $x$ modulo $N$ and an odd $m$,
write $(x/m)$ for the Jacobi symbol $(a/m)$ of the representative $0 \le a < N$ of $x$. Let $U(m)$
be the group of units of $\mathbb{Z}_m = \mathbb{Z}/m\mathbb{Z}$, let
$S(n') = \{y \in U(n') : (y/n') = 1\}$ and $L(n;p') = \{x \in U(n) : (x/n) = (x/p')\}$, and for
$m \mid n$ let $f_{n,m} : \mathbb{Z}_n \to \mathbb{Z}_m$ be reduction modulo $m$. Then for every
$y \in S(n')$ and every $z \in U(p')$ there is $x \in L(n;p')$ with $f_{n,n'}(x) = y$ and
$f_{n,p'}(x) = z$. That is, the Chinese remainder isomorphism
$\psi = (f_{n,n'}, f_{n,p'}) : U(n) \to U(n') \times U(p')$ satisfies
$S(n') \times U(p') \subseteq \psi(L(n;p'))$.

## Sources

- Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 31 (`jis-2024-24.1.7-lem-31`).
