# Fredholm setup

The coefficient linearization is a Fredholm operator. This is automatic
in finite dimensions (every linear map between finite-dimensional spaces is Fredholm) and uses no
criticality hypothesis; the Turing-specific content is the kernel and range computation in
`modeOperator_eq_zero_iff` and `exists_modeOperator_eq_iff`.
