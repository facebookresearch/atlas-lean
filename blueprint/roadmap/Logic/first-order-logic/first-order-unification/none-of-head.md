# Failure is correct when the first equation has no unifier

Let $E$ be a list of
equations between terms and let $u = v$ be a further equation, where $u\sigma$ denotes the
result of applying a substitution $\sigma$ to $u$. If $u\sigma \ne v\sigma$ for every
substitution $\sigma$, then returning no substitution meets the unification specification for
the list obtained by putting $u = v$ in front of $E$: no substitution unifies that list.
