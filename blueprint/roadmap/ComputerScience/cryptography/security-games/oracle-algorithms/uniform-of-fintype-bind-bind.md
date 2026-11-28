# Two independent uniform samples are a uniform pair

For finite nonempty types `α` and `β` and `g : α → β → PMF γ`, sampling `a`
uniformly from `α`, then `b` uniformly from `β`, then `g a b`, is the same
distribution as sampling a pair `p` uniformly from `α × β` and then `g p.1
p.2`.

Taking `g a b = PMF.pure (f (a, b))` gives the special case for a function
`f : α × β → γ`: mapping `f` over a uniform pair is equivalent to sampling
two independent uniform coordinates and applying `f` to the result.
