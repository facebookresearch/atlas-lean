# Pansiot's classification of the factor complexity of pure morphic words

Let $A$ be a
finite alphabet, let $\sigma$ be a morphism of the free monoid on $A$ that is non-erasing
(no $\sigma(x)$ is empty), let $a \in A$, and let $w = w_0 w_1 w_2 \cdots$ be an infinite word
over $A$ that is a pure fixed point of $\sigma$ from $a$: $\sigma^n(a)$ is a prefix of $w$ for
every $n \ge 0$, and the length $|\sigma^n(a)|$ tends to infinity. Assume that every letter of
$A$ occurs in $w$ and that $w$ is not eventually periodic, and let $p_w$ be the factor
complexity of $w$. A letter $x$ is bounded if $|\sigma^n(x)|$ is bounded in $n$, and $\sigma$
is everywhere growing if no letter is bounded. Call $\sigma$ quasi-uniform if for some real
$\beta \ge 1$ every letter $x$ has $|\sigma^n(x)| = \Theta(\beta^n)$; polynomially diverging if
for some real $\beta > 1$ and some $\alpha : A \to \mathbb{N}$ that is not identically zero,
every letter $x$ has $|\sigma^n(x)| = \Theta(n^{\alpha(x)} \beta^n)$; and exponentially
diverging if there are letters $x_1, x_2$, natural numbers $\alpha_1, \alpha_2$ and reals
$\beta_1 \ne \beta_2$, both greater than $1$, with
$|\sigma^n(x_i)| = \Theta(n^{\alpha_i} \beta_i^n)$ for $i = 1, 2$. All asymptotics are as
$n \to \infty$. Then:
(i) if $\sigma$ is everywhere growing and quasi-uniform, then $p_w(n) = O(n)$;
(ii) if $\sigma$ is everywhere growing and polynomially diverging, then
$p_w(n) = \Theta(n \log \log n)$;
(iii) if $\sigma$ is everywhere growing and exponentially diverging, then
$p_w(n) = \Theta(n \log n)$;
(iv) if $\sigma$ is not everywhere growing and infinitely many factors of $w$ consist of
bounded letters only, then $p_w(n) = \Theta(n^2)$;
(v) if $\sigma$ is not everywhere growing and only finitely many factors of $w$ consist of
bounded letters only, then there are a finite alphabet $B$, a letter $b \in B$, an everywhere
growing morphism $\tau$ of the free monoid on $B$, an infinite word $v$ over $B$ that is a
pure fixed point of $\tau$ from $b$, and a non-erasing morphism $\varphi$ from the free monoid
on $B$ to the free monoid on $A$, such that $w$ is the image of $v$ under $\varphi$ (for every
$n$ the word $\varphi(v_0 \cdots v_{n-1})$ is a prefix of $w$, and its length tends to
infinity) and $p_w(n) = \Theta(p_v(n))$, where $p_v$ is the factor complexity of $v$.

The quoted statement omits the hypotheses that $w$ is not eventually periodic and that every
letter of $A$ occurs in $w$, which the $\Theta$ lower bounds need. Without the first, the
morphism $a \mapsto ab$, $b \mapsto b$ fails case (iv), since its fixed point $abbb\cdots$ has
only two factors of each positive length. Without the second, letters absent from $w$ can
change the growth class of $\sigma$ without changing $w$.

## Sources

- Fabien Durand, Julien Leroy, and Gwenaël Richomme, "Do the Properties of an S-adic Representation Determine Factor Complexity?", Journal of Integer Sequences 16 (2013), Article 13.2.6, Theorem [Pansiot] (label `thm: pansiot`), lines 267–283, quoting J.-J. Pansiot, <https://cs.uwaterloo.ca/journals/JIS/VOL16/Durand/durand2.tex>.
