# Veltkamp splitting algorithm

At precision `p`, first round `(2^s + 1) * a`, then round
its difference with `a`; subtract that second result from the first and round to obtain the
high part. The low part is the rounded difference between `a` and the high part.
