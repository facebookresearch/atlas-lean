# Shamir authorized coalitions

Let `F` be a field and `Party` a finite type, with Shamir parameters `params`
of threshold `t = params.threshold`. A coalition `s` is authorized if and only
if `t < s.card`: reconstruction needs `t + 1` shares, and coalitions of size
at most `t` are unauthorized.
