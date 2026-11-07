# Under strict growth, a fixed-point set is the generated set

Let $F$ be a finite set of
functions $\mathbb{N} \to \mathbb{N}$ with $x < f(x)$ for every $f \in F$ and every
$x \in \mathbb{N}$, let $s \in \mathbb{N}$, and let $C \subseteq \mathbb{N}$ be a fixed-point set
for $F$ and $s$: $y \in C$ exactly when $y = s$ or $y = f(x)$ for some $f \in F$ and $x \in C$.
Then $C$ equals the set generated from $s$ by $F$, the numbers obtained from $s$ by applying
finitely many functions of $F$.

The proof is by strong induction: if an element of $C$ is $f(x)$ with $f \in F$ and $x \in C$,
then strict growth gives $x < f(x)$.
