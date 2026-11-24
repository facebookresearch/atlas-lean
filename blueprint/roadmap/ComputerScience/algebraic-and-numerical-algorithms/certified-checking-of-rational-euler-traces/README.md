# Certified checking of rational Euler traces

## The trace checker and its soundness

- [Checker for a trace of Euler cooling coefficients](check-thermal-trace.md)
- [An accepted trace is the sequence of powers of 9/10](check-thermal-trace-sound.md)
- [An accepted trace ends at (9/10)^10](check-thermal-trace-terminal.md)

## The reconstructed endpoint temperature

- [Endpoint temperature reconstructed from a trace](trace-endpoint.md)
- [The endpoint of an accepted trace is the tenth Euler iterate](trace-endpoint-eq-iterate.md)
- [The endpoint of an accepted trace is within a tenth of the excess](trace-endpoint-error.md)

## Digit runs and their values

- [Value of a decimal digit character](digit-value.md)
- [Positional value of a run of digits](decimal-value.md)
- [Run of one to eleven decimal digits](is-decimal-digits.md)
- [Bounded decoding of a decimal digit run](decode-decimal.md)
- [A digit run decodes exactly when well formed, to its positional value](decode-decimal-eq-some-iff.md)

## Tokens and their decoding

- [Token of an encoded trace as written](trace-token.md)
- [Characters of a trace token](encode.md)
- [Integer denoted by the numerator of a trace token](numerator.md)
- [Natural number denoted by the denominator of a trace token](denominator.md)
- [Admissible trace token](admissible.md)
- [Rational value of a trace token](value.md)
- [Decoding the numerator of a trace token](decode-numerator.md)
- [Decoding the denominator of a trace token](decode-denominator.md)
- [Splitting a character list at a separator](split-on-char.md)
- [Decoding one trace token](decode-token.md)
- [A token decodes exactly when it encodes an admissible token](decode-token-eq-some-iff.md)

## Decoding a whole trace

- [Decoding an encoded trace](decode-trace.md)
- [A trace decodes exactly when it joins eleven admissible tokens](decode-trace-eq-some-iff.md)
- [A trace is rejected exactly when it is not eleven admissible tokens](decode-trace-eq-none-iff.md)

## Checking an encoded trace

- [Decode-then-check of an encoded trace](check-encoded-trace.md)
- [An encoding is accepted exactly when its decoded list is accepted](check-encoded-trace-eq-true-iff.md)
- [An encoding is accepted exactly when it decodes to the powers of 9/10](check-encoded-trace-eq-true-iff-decode-t.md)
- [The decoded list of an accepted encoding is the powers of 9/10](check-encoded-trace-sound.md)
