# An encoding is accepted exactly when it decodes to the powers of 9/10

For a list of characters `s`, the [encoded-trace checker](check-encoded-trace.md) accepts `s` if and
only if `s` [decodes](decode-trace.md) to the list `((9/10)^0, (9/10)^1, …, (9/10)^10)`.
