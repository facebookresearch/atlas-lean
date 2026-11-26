# Uniformly Poly Time₂

A family of binary functions is uniformly polynomial-time on given bitstring encodings if
one polynomial-time machine evaluates it at every parameter. It receives the encoded triple
(parameter, first argument, second argument) and returns the encoding of the value. Only its
answers on valid triples are prescribed. The time bound is polynomial in the encoded input
length; it does not vary with the parameter.
