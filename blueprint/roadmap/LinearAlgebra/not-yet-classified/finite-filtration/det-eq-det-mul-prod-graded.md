# Det eq det mul prod graded

The determinant on the final stage of a finite invariant filtration is
the determinant on the initial stage times the product of the determinants
on all successive graded quotients.

The stages may be presented as different module types.  Each `step i`
identifies stage `i` with an invariant submodule of stage `i+1`; this avoids
choosing coercion-heavy nested subtypes and makes the theorem convenient for
filtrations transported through canonical linear equivalences.
