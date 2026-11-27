# Head-tail recursion of the ordered multilinear iteration

Let R be a commutative ring with a topology, V an R-module, A,C_n topological R-module
objects, κ:V→A linear, u∈C_0 and bilinear steps b_n:A×C_n→C_(n+1). Define F_0=u and
F_(n+1)(v₀,…,v_n)=b_n(κ(v₀),F_n(v₁,…,v_n)). For v=(v₀,…,v_n),
iterateCupMultilinear(n+1)(v)=b_n(κ(v₀),iterateCupMultilinear n(v₁,…,v_n)).
