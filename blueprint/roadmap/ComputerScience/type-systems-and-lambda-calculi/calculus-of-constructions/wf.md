# Well-formed contexts

A context is a list of terms whose head is the most recent binding.
Well-formedness of contexts is defined together with the typing judgement
$\Gamma \vdash t : A$ as the least predicate such that the empty context is well formed, and
if $\Gamma$ is well formed and $\Gamma \vdash A : s$ for some sort $s$, then the context
obtained from $\Gamma$ by adding $A$ at the head is well formed.
