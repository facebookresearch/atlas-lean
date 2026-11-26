# Rational certificates for explicit Euler cooling traces

## The trace checker

- [Thermal trace checker](check-thermal-trace.md)

## Soundness

- [Terminal value of an accepted thermal trace](check-thermal-trace-terminal.md)
- [Soundness of the thermal trace checker](check-thermal-trace-sound.md)

## The physical endpoint and its analytic bound

- [Endpoint reconstructed from a thermal trace](trace-endpoint.md)
- [Certified thermal endpoint is the tenth Euler iterate](trace-endpoint-eq-iterate.md)
- [Error bound for the certified thermal endpoint](trace-endpoint-error.md)

## Bounded decoding of an encoded trace

- [Value of a decimal digit character](digit-value.md)
- [Positional value of a run of decimal digits](decimal-value.md)
- [Decimal digit run of bounded length](is-decimal-digits.md)
- [Bounded decimal decoding](decode-decimal.md)
- [Decoding a signed numerator](decode-numerator.md)
- [Decoding a denominator](decode-denominator.md)
- [Splitting a character list at a separator](split-on-char.md)
- [Decoding a rational token](decode-token.md)
- [Thermal trace token](trace-token.md)
- [Characters of a thermal trace token](encode.md)
- [Numerator of a thermal trace token](numerator.md)
- [Denominator of a thermal trace token](denominator.md)
- [Admissible thermal trace token](admissible.md)
- [Value of a thermal trace token](value.md)
- [Token decoding inverts admissible token encoding](decode-token-eq-some-iff.md)
- [Bounded decimal decoding is exact](decode-decimal-eq-some-iff.md)
- [Bounded thermal trace decoder](decode-trace.md)
- [Trace decoding returns exactly the token values](decode-trace-eq-some-iff.md)
- [Rejection by the trace decoder](decode-trace-eq-none-iff.md)

## Replaying checked traces

- [Encoded thermal trace checker](check-encoded-trace.md)
- [Encoded trace acceptance is decoding followed by the trace checker](check-encoded-trace-eq-true-iff.md)
- [Accepted encoded traces decode to the powers of 9/10](check-encoded-trace-eq-true-iff-decode-t.md)
- [Soundness of an accepted trace encoding](check-encoded-trace-sound.md)
