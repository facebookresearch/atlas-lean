# Model terms are locally closed

Every term of the [untyped term model](model.md), defined by having no dangling bound index, is locally closed in the inductive sense: it is derived by the rules that free variables are locally closed, an application of locally closed terms is locally closed, and an abstraction $\lambda.b$ is locally closed when $b$ opened with every name outside some finite set is locally closed.
