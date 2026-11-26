# Correct

Correctness on a circuit class (Gentry, Definition 2.1.1). One negligible bound in the
security parameter works for every generated key pair, input arity, permitted circuit, message
tuple and tuple of supported fresh ciphertexts. With these fixed, the probability that evaluation
decrypts to anything other than the circuit output (including rejection) is at most the bound.
