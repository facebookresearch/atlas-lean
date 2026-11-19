# Denotation of simple types

Given an interpretation $I$ assigning a type $I(b)$ to each
base type $b$, the denotation $[\![A]\!]_I$ of a simple type $A$ is defined by recursion on $A$:
a base type $b$ denotes $I(b)$, and a function type $A \Rightarrow B$ denotes the type of all
functions from $[\![A]\!]_I$ to $[\![B]\!]_I$.
