# Program steps of the calculus with callcc

For an admissible evaluation context `E`: a
local reduction in the hole of `E`; `E[callcc v]` steps to `E[v (λx. abort E[x])]` for a value
`v` (Wright and Felleisen's rule callcc); and `E[abort e]` steps to `e` (rule abort).
