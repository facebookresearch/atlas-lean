# Constants

A signature of finitely many constants over base types $B$: a typing context
$\Gamma_0$, a list binding each constant name to a type scheme, an arity for each name, and the
predicate telling the constructors apart from the destructors. The context is closed: the
visible scheme of each name, the scheme of its first binding in $\Gamma_0$, has no free type
variable. A binding shadowed by an earlier binding of the same name is not visible and may have
free type variables. Pottier and Rémy allow the set of constants to be finite or infinite
(§10.1); here it is the finite set of names bound by $\Gamma_0$.
