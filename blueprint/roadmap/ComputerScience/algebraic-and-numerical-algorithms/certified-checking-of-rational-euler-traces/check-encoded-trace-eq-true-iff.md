# An encoding is accepted exactly when its decoded list is accepted

For a list of characters `s`, the [encoded-trace checker](check-encoded-trace.md) accepts `s` if and
only if `s` [decodes](decode-trace.md) to a list `y` that the
[trace checker](check-thermal-trace.md) accepts.
