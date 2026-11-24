# A trace is rejected exactly when it is not eleven admissible tokens

For a list of characters `s`, the [trace decoder](decode-trace.md) returns nothing on `s` if and
only if it is not the case that `s` has at most 300 characters and is obtained by joining with `,`
the [encodings](encode.md) of eleven [admissible](admissible.md) tokens.
