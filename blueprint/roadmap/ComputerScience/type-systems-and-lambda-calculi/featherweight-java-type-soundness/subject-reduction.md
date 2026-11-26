# Subject reduction for the call-by-value `Step`

**Subject reduction for the call-by-value `Step`** (TOPLAS Theorem 2.4.1, whose relation
 is nondeterministic). In a valid class table and any context, a step from an expression of
 type `C` reaches an expression typed at a subtype of `C`. The type can shrink (an upcast
 steps to the object it casts, and a method body can type below the declared return type), and
 the stupid cast T-SCast is needed when a cast subject steps (TOPLAS p. 405).
