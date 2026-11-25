# Uniform key-derivation function

For finite nonempty sets $G$ and $K$, a function $H : G \to K$ is a uniform key-derivation function
when it maps the uniform distribution on $G$ to the uniform distribution on $K$. This is a property of
a fixed function, which the eavesdropper may know, not a random oracle; Katz and Lindell
(Section 11.4.2) use a hash function with this property.
