# Solutions of locally Lipschitz ODEs that leave every compact set

Let $E$ be a real
Banach space, let $U \subseteq \mathbb{R} \times E$ be open, let $(t_0, x_0) \in U$, and let
$f : \mathbb{R} \times E \to E$ be continuous on $U$ and locally Lipschitz in the state variable,
uniformly in time: every $p \in U$ has a neighbourhood $N$ and a constant $C \ge 0$ such that
$\|f(t, u) - f(t, w)\| \le C \|u - w\|$ whenever $(t, u)$ and $(t, w)$ lie in $N \cap U$. Then
there are an open interval $I$ (possibly unbounded) containing $t_0$ and a function
$x : \mathbb{R} \to E$ with $x(t_0) = x_0$ such that $(t, x(t)) \in U$ and
$x'(t) = f(t, x(t))$ for every $t \in I$, and such that for every compact $K \subseteq U$ there
are $c_1, c_2 \in I$ with $(t, x(t)) \notin K$ for every $t \in I$ with $t \ge c_1$ and for
every $t \in I$ with $t \le c_2$.

Proof: local Picard--Lindelöf solutions are glued by uniqueness into Teschl's maximal solution
(Theorem 2.13).  A compactly recurrent finite endpoint extends by Lemma 2.14, giving the two exit
statements of Corollaries 2.15--2.16.

## Sources

- G. Teschl, Ordinary Differential Equations and Dynamical Systems, Section 2.4.
