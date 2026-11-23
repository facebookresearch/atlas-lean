# Specification of a unification result

Let $E$ be a list of equations between terms and
$r$ either a substitution or failure. The specification holds for $E$ and $r$ when, if $r$ is a
substitution $s$, then $s$ unifies $E$ and every substitution $s'$ that unifies $E$ equals the
composite substitution that applies first $s$ and then $s'$; and, if $r$ is failure, then no
substitution unifies $E$.
