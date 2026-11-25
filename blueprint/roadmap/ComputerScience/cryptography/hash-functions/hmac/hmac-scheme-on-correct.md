# Correctness of HMAC on encoded messages

For every encoding `enc : X → List Bool`, the HMAC scheme on `enc` is correct
(Katz and Lindell, Definition 4.1): honestly computed tags verify.
