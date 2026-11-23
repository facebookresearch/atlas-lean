# Arc consistency after one AC-3 revision

Let $P$ be a binary CSP whose constraints are
symmetric, that is the arc $(x, y)$ allows $(a, b)$ exactly when the arc $(y, x)$ allows $(b, a)$.
Let $\mathrm{dom}$ be domains, let $x \ne y$ be variables, let $R$ be the set of values
$a \in \mathrm{dom}(x)$ for which some $b \in \mathrm{dom}(y)$ has the arc $(x, y)$ allowing
$x = a$ together with $y = b$, and let $\mathrm{dom}'$ be $\mathrm{dom}$ with the domain of $x$
replaced by $R$. Let $e$ be an arc of $P$ with two distinct endpoints such that $e = (x, y)$ or
$e$ is consistent with respect to $\mathrm{dom}$, and such that, if $R \ne \mathrm{dom}(x)$, then
$e$ is not of the form $(z, x)$ with $z \ne y$. Then $e$ is consistent with respect to
$\mathrm{dom}'$.
