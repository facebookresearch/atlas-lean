# The universal-bar component applies the monoid map before the power comparison

Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. For an internal-monoid morphism f:M→N, let φ_X=f⊗id_X and
q_n:T_M^n(I)→T_N^n(I) be the component of the induced power morphism. For every n≥0,
E(f)_n=φ_\{T_M^n(I)\}≫T_N(q_n):T_M(T_M^n(I))→T_N(T_N^n(I)). The first map replaces the outer
M-factor by N; the second is id_N tensored with q_n.
